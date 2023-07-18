from typing import List, Dict, Set, Callable
from itertools import combinations

from splitting.abstract_node import AbstractNode

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
            if self.__graph.is_merging_make_a_cycle(v1, v2):
                continue
            new_graph, mapping = self.__graph.clone()
            new_graph.merge(mapping[v1], mapping[v2])
            mapping[v1].merge(mapping[v2])
            self.__add_statics(mapping[v1])
            overlap = len(v1.args & v2.args) / (1e-9 + len(v1.args | v2.args))  # Adding epsilon to prevent division by zero
            result.append(ArecesNode(new_graph, overlap))
        return result

    def ordered_micro_actions(self):
        return self.__graph.topological_order(lambda v: len(v.preconditions))
    
    def should_be_pruned(self, __o: 'ArecesNode') -> bool:
        return False
    
    def is_promising(self, previous_best: 'ArecesNode') -> bool:
        return self.cost[0] <= previous_best.cost[0]

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
        ground_size = sum(self.count_estimate(m) for m in self.__graph.vertices)
        over_threshold = max(0, ground_size - self.ground_size_threshold)

        ## Considering Introduced args
        ## A chain of micro actions with a sequence of lower introducing args
        ## is consider a better chain.
        ordered = self.ordered_micro_actions()
        introduced_args = []
        args = set()
        for micro_action in ordered:
            new_args = micro_action.args - args
            introduced_args.append(len(new_args))
            args.update(new_args)

        return (over_threshold,
                len(self.__graph.vertices),
                introduced_args,
                ground_size)