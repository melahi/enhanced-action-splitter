from typing import List, Set, Dict, Iterable
from itertools import permutations, product
from functools import reduce
import math

from pddl import Atom

from .abstract_node import AbstractNode
from .micro_action import MicroAction, Condition, TypedObject
from .graph import Graph
from .knowledge import Knowledge


class Node(AbstractNode):
    size_threshold: int
    action_args: Set[str]
    statics: List[Condition]
    preconditions_vars: Set[str]
    positive_vars: Set[str]
    dependency_graph: Graph[MicroAction]
    knowledge: Knowledge
    memoized_estimate = {}

    @classmethod
    def get_omittable_variables(cls, condition: Condition):
        literal = condition.condition
        predicate = (literal.predicate,
                     [a.name if isinstance(a, TypedObject) else a
                      for a in literal.args])
        return {a
                for a in cls.knowledge.omittable_arguments(predicate)
                if a.startswith("?")}

    @classmethod
    def prepare_class_variables(cls,
                                preconditions: List[MicroAction],
                                transitions: List[MicroAction],
                                size_threshold: int,
                                knowledge: Knowledge,
                                action_args: Set[str],
                                distinct_args: Dict[str, Set[str]]):
        cls.action_args = action_args
        cls.knowledge = knowledge
        cls.statics = [s
                       for p in preconditions
                       for s in p.preconditions
                       if knowledge.is_static(s.condition.predicate)]

        cls.preconditions_vars = set().union(*(p.args for p in preconditions))
        positive_preconditions = [p.preconditions[0]
                                  for p in preconditions
                                  if isinstance(p.preconditions[0].condition,
                                                Atom)]
        cls.positive_vars = set().union(*(p.find_args()
                                          for p in positive_preconditions))
        cls.dependency_graph = cls.create_dependency_graph(preconditions,
                                                           transitions,
                                                           distinct_args)
        cls.size_threshold = max(size_threshold,
                                 cls.lowerbound_size(  preconditions
                                                     + transitions) + 10000)
        return cls

    @classmethod
    def create_dependency_graph(cls,
                                preconditions: List[MicroAction],
                                transitions: List[MicroAction],
                                distinct_args: Dict[str, Set[str]]):
        # Create dependency graph
        # dependency graph demonstrates dependencies among variables
        # and preconditions. We say a variable depends on a preconditions,
        # if the variable is an omittable argument of the precondition.
        # We say a precondition depends on a variable if the variable is not
        # an omittable argument of the precondition.
        def is_helping(subject: MicroAction, object: MicroAction):
            assert len(subject.preconditions) == 1,\
                "`subject` should be a precondition"
            subject: Condition = subject.preconditions[0]
            if not isinstance(subject.condition, Atom):
                return False
            assert len(object.preconditions) == 1,\
                "`object` should be a precondition"
            subject_determinable = cls.get_omittable_variables(subject)
            if len(subject_determinable) != 1:
                return False
            object_determinable = cls.get_omittable_variables(object
                                                              .preconditions[0])
            if len(object_determinable) == 1:
                object_needed = object.args - object_determinable
            else:
                # If there is more than one determinable args, then we can
                # choose any of them, depending on the value of the
                # `subject_determinable`.
                object_needed = object.args
            return not object_needed.isdisjoint(subject_determinable)

        def threatening_relation(micro_action: MicroAction,
                                 transition: MicroAction):
            if micro_action == transition:
                return False
            return micro_action.is_threatened_by(transition, distinct_args)

        def negative_condition_dependency(positive_condition: MicroAction,
                                          negative_condition: MicroAction):
            assert len(negative_condition.preconditions) == 1,\
                "`positive_condition` should have only one precondition"
            if isinstance(negative_condition.preconditions[0].condition, Atom):
                return False
            assert len(positive_condition.preconditions) == 1,\
                "`positive_condition` should have only one precondition"
            if not isinstance(positive_condition.preconditions[0].condition,
                              Atom):
                return False
            return not (negative_condition
                        .args
                        .isdisjoint(positive_condition.args))

        def find_edges(criteria, possible_edges):
            return [(m2, m1) for m1, m2 in possible_edges if criteria(m1, m2)]

        dependency_graph = Graph(preconditions + transitions)
        dependency_graph = reduce(Graph.add_edge,
                                  find_edges(is_helping,
                                             permutations(preconditions, r=2)),
                                  dependency_graph)
        dependency_graph = dependency_graph.make_acyclic()
        # dependency_graph = reduce(Graph.add_edge,
        #                           find_edges(negative_condition_dependency,
        #                                      product(preconditions, repeat=2)),
        #                           dependency_graph)
        dependency_graph = reduce(Graph.add_edge,
                                  find_edges(threatening_relation,
                                             product(  preconditions
                                                     + transitions,
                                                     transitions)),
                                  dependency_graph)
        return dependency_graph

    @classmethod
    def count_estimate(cls, micro_action: MicroAction, args=None) -> int:
        args = micro_action.args if args is None else args
        statics = [p
                  for p in micro_action.preconditions
                  if p in cls.statics]
        key = (frozenset(args), tuple(statics))
        if key not in cls.memoized_estimate:
            typed_args = [a for a in cls.action_args if a.name in key[0]]
            conditions = [c.condition for c in key[1]]
            cls.memoized_estimate[key] = (cls
                                          .knowledge
                                          .all_count_estimate(typed_args,
                                                              conditions))
        return cls.memoized_estimate[key]

    @classmethod
    def lowerbound_size(cls, micro_actions: Iterable[MicroAction]):
        #NOTE: Static conditions are not considered/supported completely!
        #      TODO: The current implementation is of supporting static
        #            conditions are not exact! It needs to be revised!
        #      
        #NOTE: Domain of arguments are assumbed to be have more
        #      than one elements.
        accumulated_size = 0
        dynamics = []
        static_micro_action = MicroAction()
        for micro_action in micro_actions:
            for precondition in micro_action.preconditions:
                if precondition in cls.statics:
                    static_micro_action.merge(micro_action)
                    break
            else:
                dynamics.append(micro_action)
        micro_actions = dynamics
        if static_micro_action.preconditions:
            micro_actions += [static_micro_action]
        micro_actions.sort(key=lambda m: len(m.args), reverse=True)
        filtered_micro_actions = []
        for micro_action in micro_actions:
            for micro_action2 in filtered_micro_actions:
                if micro_action2.args.issuperset(micro_action.args):
                    break
            else:
                filtered_micro_actions.append(micro_action)
        for micro_action in filtered_micro_actions:
            # args = micro_action.args - static_micro_action.args
            # accumulated_size += cls.count_estimate(micro_action, args)
            accumulated_size += cls.count_estimate(micro_action)
        return accumulated_size

    def __init__(self,
                    micro_actions: List[MicroAction],
                    preconditions: List[MicroAction],
                    transitions: List[MicroAction],
                    fixed_ground_size: int  # The ground size of
                                            # `micro_actions[:-1]`
                ):
        # NOTE: `micro_actions[:-1]` are fixed; we can/should only
        #        modify the `micro_actions[-1]`.
        self.__micro_actions = micro_actions  #chained micro-actions
        self.__preconditions = [] # preconditions  # remaining preconditions
        for precondition in preconditions:
            if not precondition.args:
                self.__micro_actions[-1].merge(precondition)
            else:
                self.__preconditions.append(precondition)
        self.__transitions = [] # transitions  # remaining transitions
        for transition in transitions:
            if not transition.args:
                self.__micro_actions[-1].merge(transition)
            else:
                self.__transitions.append(transition)
        self.__visit_time = {}
        for i, micro_action in enumerate(self.__micro_actions):
            for arg in micro_action.args:
                self.__visit_time.setdefault(arg, i)
        self.__fixed_ground_size = fixed_ground_size
        self.__key = tuple((frozenset(m.preconditions),
                            frozenset(m.transitions))
                            for m in micro_actions)
        self.__cost = None

    def __str__(self):
        pre = []
        for m in self.__micro_actions:
            pre.append(''.join(sorted([p.to_string("   ")
                                        for p in m.preconditions])))
        return (  "---------------\n" + '++++++++++\n'.join(pre)
                + f"\n====== {self.cost} =======\n")

    def __hash__(self) -> int:
        return hash(self.__key)

    def __eq__(self, __o: 'Node') -> bool:
        return self.__key == __o.__key

    def __lt__(self, __o: 'Node') -> bool:
        return self.cost < __o.cost

    @property
    def cost(self):
        if self.__cost is None:
            self.__cost = self.__calculate_cost()
        return self.__cost

    def ordered_micro_actions(self):
        assert not self.__preconditions and not self.__transitions,\
                "Expected not having remaining precondition or "\
                "transition"
        return self.__micro_actions.copy()

    def neighbors(self) -> List['Node']:
        if not self.__preconditions and not self.__transitions:
            # It is a terminal node
            return []

        # if not self.__micro_actions[-1].args:
        #     for micro_action in self.__preconditions:
        #         for arg in micro_action.args:
        #             if arg not in self.__visit_time:
        #                 break
        #         else:
        #             new_micro_action = self.__micro_actions[-1].copy()
        #             new_micro_action.merge(micro_action)
        #             estimate = self.count_estimate(new_micro_action)
        #             child = self.__get_child(new_micro_action, estimate)
        #             if not child.__preconditions and not self.__transitions:
        #                 return [child]
        #             child.__micro_actions.append(MicroAction())
        #             return child.neighbors()

        last = self.__micro_actions[-1]
        current_size = self.__fixed_ground_size + self.count_estimate(last)
        max_size = max(current_size, self.size_threshold)
        nodes = []
        for choice in self.__find_choices():
            new_micro_action = last.copy()
            new_micro_action.merge(choice)
            estimate = self.count_estimate(new_micro_action)
            possible_child = self.__get_child(new_micro_action, estimate)
            if last.args and possible_child.__get_lowerbound_size() > max_size:
                continue
            nodes.append(possible_child)
        if last.args:
            nodes.extend(Node(  self.__micro_actions
                              + [MicroAction()],
                              self.__preconditions,
                              self.__transitions,
                              current_size)
                             .neighbors())
        return nodes

    def should_be_pruned(self, other: 'Node') -> bool:
        other_cost = other.cost
        if other_cost[0] != 0:
            # we assumed `other` node is completed. This
            # condition is not complete, because we cannot check
            # the remaining number of `other`s transitions.
            return False
        return other_cost[1:] <= self.cost[1:]

    def __get_lowerbound_size(self):
            estimate = self.count_estimate(self.__micro_actions[-1])
            lowerbound = self.lowerbound_size(  self.__preconditions
                                              + self.__transitions)
            return self.__fixed_ground_size + estimate + lowerbound

    def __find_choices(self) -> List[MicroAction]:
        determined = set().union(*[m.args for m in self.__micro_actions])
        def are_relevant_vars(needed: set, all: set, relevant: set):
            # The following case is handled in the `__init__` function
            # if not all:
            #     return True
            if not determined.issuperset(needed):
                return False
            if relevant.isdisjoint(all):
                return False
            if (not self.preconditions_vars.issuperset(all)
                and not determined.issuperset(self.preconditions_vars)):
                return False
            return True

        preconditions: List[MicroAction] = []
        relevant_vars = [self.__micro_actions[-1].args,
                         determined,
                         {a.name for a in self.action_args}]
        if not relevant_vars[0]:
            del relevant_vars[0]

        for relevant in relevant_vars:
            for precondition in self.__preconditions:
                condition = precondition.preconditions[0]
                if isinstance(condition.condition, Atom):
                    needed = {}
                else:
                    needed = self.positive_vars & precondition.args
                if (    are_relevant_vars(needed, precondition.args, relevant)
                    and not any(n in self.__preconditions
                                for n in (self
                                          .dependency_graph
                                          .neighbors(precondition)))):
                    preconditions.append(precondition)
            if preconditions:
                break

        if not self.__micro_actions[-1].args:
            known_preconditions = []
            determined_args = {a for a in self.__visit_time}
            for precondition in preconditions:
                if precondition.args.issubset(determined_args):
                    known_preconditions.append(precondition)
                    continue
                omittable_args = self.get_omittable_variables(precondition.preconditions[0])
                omittable = precondition.args - determined_args
                if len(omittable) == 1 and omittable.issubset(omittable_args):
                    known_preconditions.append(precondition)

            if known_preconditions:
                preconditions = known_preconditions
            # else :
            #     first_visited_args = [(p, min(self.__visit_time.get(a, float('inf'))
            #                                   for a in p.args))
            #                           for p in preconditions]
            #     min_first = min(v[1] for v in first_visited_args)
            #     preconditions = [v[0]
            #                      for v in first_visited_args
            #                      if v[1] == min_first]

        if preconditions:
            return preconditions
        relevant_vars = relevant_vars[-1:]
        transitions = [t
                       for t in self.__transitions
                       if (    are_relevant_vars(  t.args
                                                 & self.preconditions_vars,
                                                 t.args,
                                                 relevant_vars[0])
                           and not any(n in (  self.__preconditions
                                                + self.__transitions)
                                        for n in (self
                                                  .dependency_graph
                                                  .neighbors(t))))]

        return transitions

    def __calculate_cost(self):
        ground_estimate = (  self.__fixed_ground_size
                           + self.count_estimate(self.__micro_actions[-1])
                           + self.lowerbound_size(  self.__preconditions
                                                  + self.__transitions))
        visited_new_preconditions = []
        visited_preconditions = set()
        branching_micro_actions = []
        determined_args = set()
        for micro_action in self.__micro_actions:
            visited_new_preconditions.append(0)
            branching_micro_actions.append(0)
            if not micro_action.args.issubset(determined_args):
                branching_micro_actions[-1] = 1
                determined_args |= micro_action.args
            for precondition in micro_action.preconditions:
                if precondition in visited_preconditions:
                    continue
                visited_preconditions.add(precondition)
                visited_new_preconditions[-1] += 1
        
        visited_new_preconditions [-1] += len(self.__preconditions)
        if branching_micro_actions[-1] == 0:
            for micro_action in self.__preconditions + self.__transitions:
                if not micro_action.args.issubset(determined_args):
                    branching_micro_actions[-1] = 1
                    break

        return (len(self.__preconditions),
                max(0, ground_estimate - self.size_threshold),
                sum(branching_micro_actions),
                int(math.log(ground_estimate, 2)),
                [-1 * p for p in visited_new_preconditions],
                ground_estimate)

    def __get_child(self,
                    new_micro_action: MicroAction,
                    current_estimate: int) -> 'Node':
        # Adding static precondition as much as possible
        level_off = False
        while not level_off:
            level_off = True
            for static_condition in self.statics:
                if static_condition in new_micro_action.preconditions:
                    continue
                temp = new_micro_action.copy()
                temp.add_precondition(static_condition)
                estimate = self.count_estimate(temp)
                if estimate <= current_estimate:
                    current_estimate = estimate
                    new_micro_action = temp
                    # Imposing a new condition/constraint might limit
                    # the possibilities so we can add some other
                    # static conditions. Therefore, we set `level_off`
                    # to `False`.
                    level_off = False

        # Include all preconditions having a subset of arguments
        level_off = False
        remaining_preconditions: List[MicroAction] = self.__preconditions
        while not level_off:
            level_off = True
            new_remaining_preconditions: List[MicroAction] = []
            for precondition in remaining_preconditions:
                # omittables = self.get_omittable_variables(precondition.preconditions[0])
                # needed_args = precondition.args - omittables
                # if new_micro_action.args.issuperset(needed_args):
                if new_micro_action.args.issuperset(precondition.args):
                    # This addition might be redundant; `precondition`
                    # might already exist in the `new_micro_action`.
                    new_micro_action.merge(precondition)
                    level_off = False
                else:
                    new_remaining_preconditions.append(precondition)
            remaining_preconditions = new_remaining_preconditions

        # Include all transitions having a subset of arguments which
        # threat no remaining precondition or transition!
        remaining_transitions = self.__transitions.copy()
        fixed_conditions = set().union(*(m.preconditions
                                        for m in (self.__micro_actions[:-1]
                                                    + [new_micro_action])))
        fixed_conditions = [c.condition for c in fixed_conditions]

        def is_it_safe_to_include(transition: MicroAction):
            if not new_micro_action.args.issuperset(transition.args):
                return False

            if any(n in remaining_preconditions + remaining_transitions
                    for n in self.dependency_graph.neighbors(transition)):
                return False
            return True
        level_off = False
        while not level_off:
            for transition in remaining_transitions.copy():
                if (set(transition.transitions)
                    .issubset(new_micro_action.transitions)):
                    remaining_transitions.remove(transition)
                    continue
                if is_it_safe_to_include(transition):
                    new_micro_action.merge(transition)
                    remaining_transitions.remove(transition)
                    break
            else:
                level_off = True

        micro_actions = self.__micro_actions[:-1] + [new_micro_action]
        return Node(micro_actions,
                    remaining_preconditions,
                    remaining_transitions,
                    self.__fixed_ground_size)
