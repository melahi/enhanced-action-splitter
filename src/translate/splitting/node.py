from typing import List, Set, Dict
from itertools import permutations, product
from functools import reduce

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
                                                     + transitions))
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
    def lowerbound_size(cls, micro_actions: List[MicroAction]):
        #NOTE: Static conditions are not considered/supported!
        #NOTE: Domain of arguments are assumbed to be have more
        #      than two elements.
        accumulated_size = 0
        micro_action = filter(lambda m: all(not m.args.issubset(n.args)
                                            for n in micro_actions
                                            if m != n),
                              micro_actions)
        for micro_action in micro_actions:
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
        self.__preconditions = preconditions  # remaining preconditions
        self.__transitions = transitions  # remaining transitions
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
        return self.__calculate_cost() < __o.__calculate_cost()

    @property
    def cost(self):
        return self.__calculate_cost()

    def ordered_micro_actions(self):
        assert not self.__preconditions and not self.__transitions,\
                "Expected not having remaining precondition or "\
                "transition"
        return self.__micro_actions.copy()

    def neighbors(self) -> List['Node']:
        if not self.__preconditions and not self.__transitions:
            # It is a terminal node
            return []

        last = self.__micro_actions[-1]
        current_size = self.__fixed_ground_size + self.count_estimate(last)
        max_size = max(current_size, self.size_threshold)
        nodes = []
        for choice in self.__find_choices():
            if choice.has_transition:
                new_micro_action = last.copy()
                new_micro_action.merge(choice)
                estimate = self.count_estimate(new_micro_action)
                child = self.__get_child(new_micro_action, estimate)
                child.__micro_actions.append(MicroAction())
                child_neighbors = child.neighbors()
                if child_neighbors:
                    return child_neighbors
                child.__micro_actions.pop()
                return [child]

            new_micro_action = last.copy()
            new_micro_action.merge(choice)
            estimate = self.count_estimate(new_micro_action)
            if (    last.args
                and self.__fixed_ground_size + estimate > max_size):
                continue
            nodes.append(self.__get_child(new_micro_action,
                                                estimate))
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

    def __find_choices(self) -> List[MicroAction]:
        determined = set().union(*[m.args for m in self.__micro_actions])
        if not self.__micro_actions[-1].args:
            for transition in self.__transitions:
                needed_args = transition.args & self.preconditions_vars
                if not determined.issuperset(needed_args):
                    continue
                if any(n in (self.__preconditions + self.__transitions)
                       for n in self.dependency_graph.neighbors(transition)):
                    continue
                return [transition]

        relevant_vars = ([determined, {a.name for a in self.action_args}]
                         if not self.__micro_actions[-1].args
                         else [set().union(*(p.find_args()
                                             for p in (self
                                                       .__micro_actions[-1]
                                                       .preconditions)
                                             if isinstance(p.condition, Atom)))])
        preconditions: List[MicroAction] = []
        for relevant in relevant_vars:
            for precondition in self.__preconditions:
                # if precondition.args.isdisjoint(relevant):
                #     #precondition with no args will be handled in `__get_child`
                #     continue
                condition = precondition.preconditions[0]
                if isinstance(condition.condition, Atom):
                    if precondition.args.isdisjoint(relevant):
                        continue
                else:
                    needed = self.positive_vars & precondition.args
                    if not determined.issuperset(needed):
                        continue
                    if not relevant.issuperset(needed):
                        continue
                if any(n in self.__preconditions
                       for n in self.dependency_graph.neighbors(precondition)):
                    continue
                preconditions.append(precondition)
            if preconditions:
                break
        return preconditions

    def __calculate_cost(self):
        # Cost criteria:
        # 1. spans of preconditional components,
        #       preconditional component:
        #          The set of micro-actions with preconditions that 
        #          are connected in the term of their sharing arguments
        # 2. number of micro-actions with preconditions,
        # 3. total number of micro-actions,
        # 4. the sum of the estimate count of grounded micro-actions.
        # TODO: Perhaps we could also consider the number of
        #       decisions (args count - useful omittable args) that
        #       we need to make, in our cost criteria
        # TODO: It is also interesting to measure the importance of
        #       each criterion.

        if self.__cost is not None:
            return self.__cost

        # Finding spans of variables
        first_visit = {}
        last_visit = {}
        visited_new_preconditions = []
        branches = []
        omittables = []
        temp_micro_action = MicroAction()
        for i, micro_action in enumerate(self.__micro_actions):
            visited_new_preconditions.append(0)
            for precondition in micro_action.preconditions:
                if precondition in temp_micro_action.preconditions:
                    continue
                temp_micro_action.add_precondition(precondition)
                for arg in precondition.find_args():
                    if arg not in first_visit:
                        first_visit[arg] = i
                    last_visit[arg] = i
                if not isinstance(precondition.condition, Atom):
                    continue
                visited_new_preconditions[-1] += 1
                if precondition not in self.statics:
                    choices = self.get_omittable_variables(precondition)
                    if choices:
                        omittables.append(choices)
            for transition in micro_action.transitions:
                temp_micro_action.add_transition(transition)
            best_branches = float('inf')
            for omittable in product(*omittables):
                free_variables = temp_micro_action.args - set(omittable)
                temp = self.count_estimate(temp_micro_action, free_variables)
                best_branches = min(best_branches, temp)
            branches.append(best_branches)

        # shared_args = {a for a in temp_micro_action.args if ((a in first_visit) and (first_visit[a] != last_visit[a]))}
        # bridge_size = self.count_estimate(temp_micro_action, shared_args)
        bridge_sizes = []
        for i in range(len(self.__micro_actions)):
            shared_args = set()
            for a, f in first_visit.items():
                if f <= i and last_visit[a] > i:
                    shared_args.add(a)
            bridge_sizes.append(self.count_estimate(temp_micro_action, shared_args))

        if len(self.__preconditions):
            # It might be possible that some remaining precondition
            # reduce the `branches`.
            branches.pop()
            visited_new_preconditions.pop()

        variables_spans = [last_visit[v] - first_visit[v]
                           for v in first_visit.keys()
                           if last_visit[v] - first_visit[v] > 0]
        variables_spans.sort(reverse=True)

        # preconditional_micro_actions_count = len(
        #     tuple(filter(lambda x:x, visited_new_preconditions)))
        ground_estimate = (  self.__fixed_ground_size
                           + self.count_estimate(self.__micro_actions[-1])
                           + self.lowerbound_size(  self.__preconditions
                                                  + self.__transitions))
        self.__cost = (len(self.__preconditions),
                        max(0, ground_estimate - self.size_threshold),
                    #    len(self.__micro_actions),
                    #    preconditional_micro_actions_count,
                    #    variables_spans,
                    #    [-1 * p for p in visited_new_preconditions],
                    #    [-1 * b for b in branches],
                    #    branches[-1],
                    #    len(variables_spans),
                    #    len(self.__micro_actions),
                    #    variables_spans,
                        len([p for p in visited_new_preconditions if p]),
                    #    len(self.__micro_actions),
                    #    ground_estimate,
                    #    list(zip(bridge_sizes, [-1 * p for p in visited_new_preconditions])),
                    #    list(zip(bridge_sizes, branches)),
                    #    bridge_sizes,
                        [-1 * p for p in visited_new_preconditions],
                        branches,
                    #    [-1 * b for b in branches],
                        ground_estimate,
                         )
        return self.__cost

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
        remaining_preconditions: List[MicroAction] = []
        for precondition in self.__preconditions:
            if new_micro_action.args.issuperset(precondition.args):
                # This addition might be redundant; `precondition`
                # might already exist in the `new_micro_action`.
                new_micro_action.merge(precondition)
            else:
                remaining_preconditions.append(precondition)

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
