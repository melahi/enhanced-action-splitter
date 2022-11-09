from typing import Iterable, List, Set, Dict, Tuple
from itertools import chain, combinations, permutations, product
from functools import reduce
from copy import deepcopy

from sccs import get_sccs_adjacency_dict
import pddl
from pddl import SimpleEffect, ConditionalEffect, Effect, Atom, NegatedAtom
from pddl import Literal, TypedObject

from .common import get_conditions
from .knowledge import Knowledge
from .micro_action import Condition, Transition, MicroAction
from .graph import Graph
from .beam_search import NodeAbstract, beam_search


BEAM_SEARCH_WIDTH = 400
print("BEAM_SEARCH_WIDTH:", BEAM_SEARCH_WIDTH)
DECISION_THRESHOLD = 2
print("DECISION THRESHOLD:", DECISION_THRESHOLD)


class Action:
    """Represents an `Action` by a chain of micro-actions

    Decomposes an action into a series of micro-actions, then
    Order them in a way to help the searching process."""

    START_PROCEDURE = "start_procedure"
    STEP_TYPE = "steps"

    def __init__(self,
                 knowledge: Knowledge,
                 action: pddl.Action,
                 size_threshold: int):
        self.__knowledge = knowledge
        self.__new_objects = []
        self.__new_predicates = []
        self.__name = action.name
        self.__args = action.parameters
        preconditions = get_conditions(action.precondition)
        self.__distinct_args = self.__find_distinct_args(preconditions)
        self.__micro_actions = self.__split_action(action, size_threshold)
        self.__chain_micro_actions(knowledge.default_objects)

    @property
    def new_objects(self):
        return self.__new_objects.copy()

    @property
    def new_predicates(self):
        return self.__new_predicates.copy()

    @property
    def name(self):
        return self.__name

    def to_string(self, indent: str) -> str:
        if len(self.__micro_actions) == 1:
            return self.__micro_actions[0].to_string(self.__name,
                                                     self.__args,
                                                     indent)
        return "\n".join(m.to_string(f"{self.__name}_{i}", self.__args, indent)
                         for i, m in enumerate(self.__micro_actions))

    def __split_action(self, action, size_threshold) -> List[MicroAction]:
        conditions = {Condition(c) for c in get_conditions(action.precondition)}
        preconditions = [MicroAction().add_precondition(c) for c in conditions]
        transitions = self.__get_transitions(action.effects)
        transitions = self.__prepare_transitions(transitions)
        # micro_actions = preconditions + transitions
        micro_actions = self.__order_micro_actions(preconditions,
                                                   transitions,
                                                   size_threshold)
        micro_actions = self.__complete_micro_actions(micro_actions, conditions)
        return micro_actions

    def __get_transitions(self, raw_effects):
        effects = []
        for effect in raw_effects:
            if isinstance(effect, SimpleEffect):
                effects.append(([], effect.effect))
            elif isinstance(effect, ConditionalEffect):
                conditions = get_conditions(effect.condition)
                effects.append((conditions, effect.effect))
            elif isinstance(effect, Effect):
                conditions = get_conditions(effect.condition)
                effects.append((conditions, effect.literal))
            else:
                raise NotImplementedError("Unknown effect!")
        transitions = []
        del_effects = []
        for conditions, effect in effects:
            if isinstance(effect, Atom):
                variables = self.__knowledge.get_variables(effect)
                transitions.append(Transition(conditions, effect, variables))
            elif isinstance(effect, NegatedAtom):
                if not self.__knowledge.get_variables(effect):
                    transitions.append(Transition(conditions, effect, set()))
                else:
                    del_effects.append((conditions, effect))
            else:
                raise ValueError("Expected only literals as effect!")
        for conditions, effect in del_effects:
            variables = self.__knowledge.get_variables(effect)
            covered_variables = set()
            for transition in transitions:
                (covered_variables
                 .update(transition
                         .check_delete_effect(variables, conditions, effect)))
            if covered_variables != variables:
                # Not all variables are covered by the current transitions;
                # it might be the case when we have state variables that just
                # falsify their values. Other probability might be that the
                # logical consequence implementation might not be precise.
                # In any case we fix it by adding a (probably redundant)
                # transition.
                transitions.append(Transition(conditions, effect, set()))
        return transitions

    def __prepare_transitions(self,
                              transitions: List[Transition]) -> List[MicroAction]:
        """Prepares the transitions

        It is important to consider the possibility that a transition
        affect other transition's condition. This relation might be
        cyclic. For example, one transition might affect the condition
        of another one, and that one might affect the first one's
        condition. Here, we find those transitions and merge them.

        Returns:
            List[MicroAction]: List of transitions
        """
        # Constructing the ordered graph
        graph = {transition: [] for transition in transitions}
        for transition1, transition2 in permutations(transitions, 2):
            if transition1.is_threatened_by(transition2, self.__distinct_args):
                graph[transition1].append(transition2)

        components = get_sccs_adjacency_dict(graph)
   
        transitions = [reduce(lambda micro_action, transition:
                                 micro_action.add_transition(transition),
                              component,
                              MicroAction())
                       for component in components]
        return transitions

    def __order_micro_actions(self,
                              preconditions: List[MicroAction],
                              transitions: List[MicroAction],
                              size_threshold: int):

        def get_args(literal: Literal):
            return [a.name if isinstance(a, TypedObject) else a
                    for a in literal.args]
        def is_variable(argument: str):
            return argument.startswith("?")
        def get_omittable_variables(literal: Literal):
            predicate = (literal.predicate, get_args(literal))
            return [a
                    for a in self.__knowledge.omittable_arguments(predicate)
                    if is_variable(a)]
        omittable_count = {c: len(get_omittable_variables(c.condition))
                           for p in preconditions
                           for c in p.preconditions}

        memoized_estimate = {}
        def count_estimate(micro_action: MicroAction) -> int:
            key = (frozenset(micro_action.args),
                   tuple(micro_action.preconditions))
            if key not in memoized_estimate:
                memoized_estimate[key] = self.__count_estimate(key[0], key[1])
            return memoized_estimate[key]

        def priority(micro_action: MicroAction):
            # Priority criteria:
            # 1. preconditions with more omittable positions,
            # 2. more preconditions,
            # 3. less number of possible ground instances.
            return (sum([omittable_count[p]
                            for p in micro_action.preconditions]),
                    len(micro_action.preconditions),
                    -1 * count_estimate(micro_action))

        class Candidate(NodeAbstract):
            def __init__(self, graph: Graph[MicroAction]):
                self.__graph = graph
                self.__order = graph.topological_order(priority)
                self.__cost = self.__calculate_cost()
                self.__key = ((tuple(m.preconditions), tuple(m.transitions))
                              for m in self.__order)

            def __hash__(self) -> int:
                return hash(self.__key)

            def __eq__(self, __o: 'Candidate') -> bool:
                return self.__key == __o.__key

            def __lt__(self, __o: 'Candidate') -> bool:
                return self.__cost < __o.__cost

            @property
            def order(self):
                return self.__order.copy()

            def neighbors(self) -> List['Candidate']:
                result = []
                for first, second in combinations(self.__order, r=2):
                    if self.__are_mergeable(first, second):
                        result.append(self.__merge(first, second))
                return result

            def __calculate_cost(self):
                # Cost criteria:
                # 1. spans of connected components of micro-action with
                #    preconditions,
                # 2. number of micro-actions with preconditions,
                # 3. total number of micro-actions,
                # 4. the estimate count of grounded actions.

                # Finding components
                components = []
                for micro_action in self.__order:
                    if not micro_action.has_precondition:
                        continue
                    new_components = []
                    new_component = micro_action.args
                    for component in components:
                        if new_component.isdisjoint(component):
                            new_components.append(component)
                        else:
                            new_component.update(component)
                    components = new_components + [new_component]

                spans = []
                for component in components:
                    first = len(self.__order)
                    last = 0
                    for i, micro_action in enumerate(self.__order):
                        if (   not micro_action.has_precondition
                            or micro_action.args.isdisjoint(component)):
                            continue
                        first = min(first, i)
                        last = max(last, i)
                    spans.append(last - first + 1)
                spans.sort(reverse=True)

                preconditions_count = 0
                ground_estimate = 0
                for micro_action in self.__order:
                    ground_estimate += count_estimate(micro_action)
                    if micro_action.has_precondition:
                        preconditions_count += 1

                return (spans,
                        preconditions_count,
                        len(self.__order),
                        ground_estimate)

            def __are_mergeable(self, first: MicroAction, second: MicroAction):
                if self.__graph.is_merging_make_a_cycle(first, second):
                    return False
                if count_estimate(first.copy().merge(second)) > size_threshold:
                    return False
                if (    first.has_precondition
                    and second.has_precondition
                    and not first.args.isdisjoint(second.args)):
                    return True
                if (    first.args.issubset(second.args)
                    and not first.has_precondition):
                    return True
                if (    second.args.issubset(first.args)
                    and not second.has_precondition):
                    return True
                return False

            def __merge(self, first: MicroAction, second: MicroAction):
                new_graph, mapping = self.__graph.clone()
                first, second = mapping[first], mapping[second]
                first.merge(second)
                new_graph.merge(first, second)
                return Candidate(new_graph)

        def build_helper_graph() -> Graph[MicroAction]:
            def is_helping(subject: MicroAction, object: MicroAction):
                for condition in [p.condition for p in subject.preconditions]:
                    if not (object
                            .args
                            .isdisjoint(get_omittable_variables(condition))):
                        return True
                return False

            graph = Graph(preconditions + transitions)
            graph = reduce(Graph.add_edge,
                           filter(lambda edge: is_helping(*edge),
                                  permutations(preconditions, r=2)),
                           graph)
            graph.make_acyclic(vertex_priority=priority)
            return graph

        def prepare_graph() -> Graph[MicroAction]:
            graph = build_helper_graph()

            # Add edges to prevent placing transitions before determining their
            # parameters.
            graph = reduce(Graph.add_edge,
                           filter(lambda edge:
                                    not edge[0].args.isdisjoint(edge[1].args),
                                  product(preconditions, transitions)),
                           graph)

            # Add edges correspond to threatening relations
            def threatening_relation(edge: Tuple[MicroAction, MicroAction]):
                if edge[0] == edge[1]:
                    return False
                return edge[0].is_threatened_by(edge[1], self.__distinct_args)
            graph = reduce(Graph.add_edge,
                           filter(threatening_relation,
                                  product(preconditions + transitions,
                                          transitions)),
                           graph)
            return graph

        initial_candidate = Candidate(prepare_graph())
        founded_candidate = beam_search(initial_candidate, BEAM_SEARCH_WIDTH)
        return founded_candidate.order

    def __complete_micro_actions(self,
                                 micro_actions: List[MicroAction],
                                 partial_state: Set[Condition]):
        """Add related conditions to each micro-action

        Find micro-action's related conditions and add them -as much as
        possible- to it. Related conditions are:

        1. static conditions overlapped with transition's
           arguments which doesn't increase the number of its
           ground instances, 
        2. conditions with the arguments which are the subset
           of the transition's arguments.
        """
        def complete(conditions: Set[Condition], micro_action: MicroAction):
            # Sort conditions to make our method deterministic (reproducible)
            conditions = sorted(conditions, key=lambda c: c.to_string(""))
            level_off = False
            current_size = self.__count_estimate(micro_action.args,
                                                 micro_action.preconditions)
            while not level_off:
                level_off = True
                best = (-1, None)
                for condition in conditions:
                    args = condition.find_args()
                    if micro_action.args.isdisjoint(args):
                        continue
                    new_args = micro_action.args | args
                    new_conditions = (  set(micro_action.preconditions)
                                      | {condition})
                    new_size = self.__count_estimate(new_args, new_conditions)
                    if new_size <= current_size and new_size > best[0]:
                        best = (new_size, condition)
                if best[1] is not None:
                    micro_action.add_precondition(best[1])
                    conditions.remove(best[1])
                    level_off = False
                    current_size = best[0]
            return micro_action

        for micro_action in micro_actions:
            complete(partial_state, micro_action)
            partial_state = (micro_action
                             .update_partial_state(partial_state,
                                                   self.__distinct_args))
        return micro_actions

    def __chain_micro_actions(self, default_values):
        assert self.__micro_actions,  "Expects one or more micro-actions"

        def use_predicate(predicate,
                          adder: MicroAction,
                          needing: List[MicroAction]):
            deleter = needing[-1]
            condition = Condition(Atom(*predicate))
            for micro_action in needing:
                micro_action.add_precondition(condition)
            if adder == deleter:
                return
            adder.add_transition(Transition([], Atom(*predicate), []))
            deleter.add_transition(Transition([], NegatedAtom(*predicate), []))

        use_predicate((self.START_PROCEDURE, ()),
                      self.__micro_actions[-1],
                      [self.__micro_actions[0]])

        procedure_name = f"{self.__name}_procedure"
        step = lambda s: f"step_{s}"
        self.__new_predicates.append((procedure_name,
                                      [TypedObject("?s", self.STEP_TYPE)],
                                      [step(0)]))
        for i in range(len(self.__micro_actions)):
            self.__new_objects.append(step(i))
            use_predicate((procedure_name, (step(i),)),
                            self.__micro_actions[i - 1],
                            [self.__micro_actions[i]])

        # Handling shared arguments
        shared_arguments = {arg.name: [] for arg in self.__args}
        argument_predicate = lambda argument: f"{self.__name}_{argument[1:]}"
        for micro_action in self.__micro_actions:
            for arg in micro_action.args:
                shared_arguments[arg].append(micro_action)
        for arg_name, shared_micro_actions in shared_arguments.items():
            if len(shared_micro_actions) < 2:
                continue
            arg = next(a for a in self.__args if a.name == arg_name)
            self.__new_predicates.append((argument_predicate(arg.name),
                                          [arg],
                                          [default_values[arg.type_name]]))
            use_predicate((argument_predicate(arg.name),
                           (default_values[arg.type_name],)),
                          shared_micro_actions[-1],
                          [shared_micro_actions[0]])
            use_predicate((argument_predicate(arg.name), (arg.name,)),
                          shared_micro_actions[0], shared_micro_actions[1:])

        return self

    def __count_estimate(self, args, conditions: Iterable[Condition]):
        args = [a for a in self.__args if a.name in args]
        conditions = [c.condition for c in conditions]
        return self.__knowledge.all_count_estimate(args, conditions)

    def __find_distinct_args(self, preconditions: List[Literal]):
        distinct_args = {}
        def get_name(arg):
            return arg.name if isinstance(arg, TypedObject) else arg
        for precondition in preconditions:
            if not isinstance(precondition, NegatedAtom):
                continue
            if precondition.predicate != "=":
                continue
            name1 = get_name(precondition.args[0])
            name2 = get_name(precondition.args[1])
            distinct_args.setdefault(name1, []).append(name2)
            distinct_args.setdefault(name2, []).append(name1)

        for arg1, arg2 in combinations(self.__args, 2):
            type1, type2 = (arg1.type_name, arg2.type_name)
            if not self.__knowledge.has_shared_elements(type1, type2):
                distinct_args.setdefault(arg1.name, []).append(arg2.name)
                distinct_args.setdefault(arg2.name, []).append(arg1.name)
        return distinct_args