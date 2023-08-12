from typing import List, Dict, Set, Callable
from itertools import combinations
import math

from pddl import Atom

from .abstract_node import AbstractNode
from .graph import Graph
from .micro_action import MicroAction, Condition
from .knowledge import Knowledge


class ArecesNode(AbstractNode):
    GAMMA = 0
    max_split_size: int
    max_interface_size: int
    __calculate_cost: Callable[['ArecesNode'], list]
    memoized_estimate = {}
    statics: Set[Condition]
    ground_size_threshold: int
    positive_args: Set[str]
    preconditional_args: Set[str]

    @classmethod
    def prepare_class_variables(cls,
                                max_split_size,
                                max_interface_size,
                                is_areces_cost,
                                knowledge: Knowledge,
                                action_args: Set[str],
                                preconditions: List[MicroAction],
                                ground_size_threshold: int):
        cls.max_split_size = max_split_size
        cls.max_interface_size = max_interface_size

        cls.__calculate_cost = (ArecesNode.__calculate_areces_cost
                                if is_areces_cost else
                                ArecesNode.__calculate_new_cost)
        cls.action_args = action_args
        cls.knowledge = knowledge
        cls.statics = {s
                       for p in preconditions
                       for s in p.preconditions
                       if knowledge.is_static(s.condition.predicate)}
        cls.ground_size_threshold = ground_size_threshold
        cls.preconditional_args = set().union(*[p.args for p in preconditions])
        cls.positive_args = set().union(*[p.args
                                          for p in preconditions
                                          if isinstance(p.preconditions[0].condition, Atom)])
        return cls

    @classmethod
    def count_estimate(cls, micro_action: MicroAction) -> int:
        static_precondition = (p
                               for p in micro_action.preconditions
                               if p in cls.statics)
        key = (frozenset(micro_action.args), tuple(static_precondition))
        if key not in cls.memoized_estimate:
            typed_args = [a for a in cls.action_args if a.name in key[0]]
            conditions = [c.condition for c in key[1]]
            cls.memoized_estimate[key] = (cls
                                          .knowledge
                                          .all_count_estimate(typed_args,
                                                              conditions))
        return cls.memoized_estimate[key]

    def __init__(self, graph: Graph[MicroAction], overlap: float):
        self.__graph = graph
        self.__key = tuple(sorted((tuple(sorted(p.to_string('')
                                                for p in m.preconditions)),
                                   tuple(sorted(t.to_string('')
                                                for t in m.transitions)))
                                  for m in graph.vertices))

        self.__overlap = overlap
        self.__cost = None

        def priority(micro_action):
            return [len([p
                         for p in micro_action.preconditions
                         if isinstance(p.condition, Atom)]),
                    len([p
                         for p in micro_action.preconditions
                         if not isinstance(p.condition, Atom)])]
        self.__order = self.__graph.topological_order(priority)

    def __hash__(self) -> int:
        return hash(self.__key)

    def __eq__(self, __o: 'ArecesNode') -> bool:
        return self.__key == __o.__key

    def __lt__(self, __o: 'ArecesNode') -> bool:
        return self.cost < __o.cost

    @property
    def cost(self):
        if self.__cost is None:
            self.__cost = self.__calculate_cost()
        return self.__cost
    
    def neighbors(self) -> List['ArecesNode']:
        result = list()
        for v1, v2 in combinations(self.__graph.vertices, r=2):
            if v1.args and v2.args and v1.args.isdisjoint(v2.args):
                continue
            if self.__graph.is_merging_make_a_cycle(v1, v2):
                continue
            new_graph, mapping = self.__graph.clone()
            new_graph.merge(mapping[v1], mapping[v2])
            mapping[v1].merge(mapping[v2])
            self.__add_statics(mapping[v1])
            overlap = len(v1.args & v2.args) / (1e-9 + len(v1.args | v2.args))  # Adding epsilon to prevent division by zero
            child = ArecesNode(new_graph, overlap)
            if not child.__does_introduce_illegal_args():
                result.append(child)
        return result

    def ordered_micro_actions(self):
        return self.__order
    
    def should_be_pruned(self, __o: 'ArecesNode') -> bool:
        return False
    
    def is_promising(self, previous_best: 'ArecesNode') -> bool:
        return self.cost[0] <= previous_best.cost[0]

    def __does_introduce_illegal_args(self) -> bool:
        determined_args = set()
        for micro_action in self.ordered_micro_actions():
            determined_args.update(*[p.find_args()
                                     for p in micro_action.preconditions
                                     if isinstance(p.condition, Atom)])
            for precondition in micro_action.preconditions:
                if isinstance(precondition.condition, Atom):
                    continue
                args = precondition.find_args()
                if not determined_args.issuperset(args & self.positive_args):
                    return True
                determined_args.update(args)

            for transition in micro_action.transitions:
                if not determined_args.issuperset(  transition.find_args()
                                                  & self.preconditional_args):
                    return True
        return False

    def __add_statics(self, micro_action: MicroAction):
        possible_improvement = True
        current_size = self.count_estimate(micro_action)
        while possible_improvement:
            for static in self.statics:
                if static in micro_action.preconditions:
                    continue
                temp = micro_action.copy().add_precondition(static)
                new_size = self.count_estimate(temp)
                if new_size <= current_size:
                    micro_action.add_precondition(static)
                    current_size = new_size
                    break
            else:
                possible_improvement = False

    def __calculate_areces_cost(self):
        split_size = len(self.__graph.vertices)
        normalized_split_size = split_size / self.max_split_size
        interface_size = max([len(m.args) for m in self.__graph.vertices])
        normalized_interface_size = interface_size / self.max_interface_size
        cost1 = (       self.GAMMA  * normalized_split_size
                 + (1 - self.GAMMA) * normalized_interface_size)
        return (cost1, -self.__overlap)

    def __calculate_new_cost(self):
        chain = self.ordered_micro_actions()
        ground_size = sum(self.count_estimate(m) for m in chain)
        visited_new_preconditions = []
        visited_preconditions = set()
        branching_micro_actions = 0
        determined_args = set()
        for micro_action in chain:
            visited_new_preconditions.append(0)
            if not micro_action.args.issubset(determined_args):
                branching_micro_actions += 1
                determined_args |= micro_action.args
            for precondition in micro_action.preconditions:
                if precondition in visited_preconditions:
                    continue
                visited_preconditions.add(precondition)
                visited_new_preconditions[-1] += 1
        return (max(0, ground_size - self.ground_size_threshold),
                branching_micro_actions,
                int(math.log(ground_size, 2)),
                [-1 * p for p in visited_new_preconditions],
                ground_size)
