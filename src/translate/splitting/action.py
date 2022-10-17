from typing import Iterable, List, Set, Dict
from itertools import chain, combinations, permutations
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

BEAM_SEARCH_WIDTH = 400


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
        return "\n".join(m.to_string(f"{self.__name}_{i}", self.__args, indent)
                         for i, m in enumerate(self.__micro_actions))

    def __split_action(self, action, size_threshold) -> List[MicroAction]:
        preconditions = get_conditions(action.precondition)
        parameters = [parameter.name for parameter in action.parameters]
        influential_order = self.__influential_order(parameters, preconditions)
        conditions = self.__order_conditions(preconditions,
                                             influential_order,
                                             size_threshold)
        transitions = self.__get_transitions(action.effects)
        preconditions = {Condition(p) for p in preconditions}
        transitions = self.__prepare_transitions(preconditions, transitions)
        micro_actions = self.__order_micro_actions(conditions, transitions)
        # micro_actions = self.__merge_micro_actions(micro_actions, 0)
        micro_actions = self.__complete_micro_actions(micro_actions,
                                                      preconditions)
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

    def __influential_order(self,
                            variables: List[str],
                            conditions: List[Literal]) -> List[str]:
        """Orders the vertices based on their influential relations"""

        # Filter out any condition except positive literals
        conditions = filter(lambda condition: isinstance(condition, Atom),
                            conditions)
        predicates = [(atom.predicate, atom.args) for atom in conditions]

        # Constructing the influential graph
        graph = Graph(variables)
        relations = list(chain(*[self.__knowledge.get_relations(predicate)
                                 for predicate in predicates]))
        graph = reduce(Graph.add_edge, relations, graph)

        return graph.topological_order()

    def __order_conditions(self,
                           conditions: List[Literal],
                           influential_order: List[str],
                           size_threshold: int) -> List[MicroAction]:
        def get_args(literal: Literal):
            return [a.name if isinstance(a, TypedObject) else a
                    for a in literal.args]
        def get_variables(literal: Literal):
            return [a for a in get_args(literal) if a.startswith("?")]
        influential_rank = {v: i for i, v in enumerate(influential_order)}
        appearance_rank = {v: float('inf') for v in influential_order}
        def get_omittable_args(literal: Literal):
            predicate = (literal.predicate, get_args(literal))
            return self.__knowledge.omittable_arguments(predicate)

        result: List[MicroAction] = []
        def get_decision(new_condition: Literal):
            conditions = [c.condition for c in result[-1].preconditions]
            conditions.append(new_condition)
            variables = {v
                         for l in conditions
                         for v in get_variables(l)
                         if appearance_rank[v] >= len(result) - 1}
            dependencies: Dict[str, List[Set[str]]] = {}
            for condition in conditions:
                if not isinstance(condition, Atom):
                    continue
                condition_vars = set(get_variables(condition)) & variables
                for omittable in get_omittable_args(condition):
                    if omittable not in condition_vars:
                        continue
                    dependency = condition_vars - {omittable}
                    dependencies.setdefault(omittable, []).append(dependency)
            def decide(determined: Set[str]) -> Set[str]:
                if variables == determined:
                    return set()
                for dependent in dependencies:
                    if dependent in determined:
                        continue
                    for dependency in dependencies[dependent]:
                        if dependency.issubset(determined):
                            determined.add(dependent)
                best_decisions = variables - determined
                for variable in variables - determined:
                    # I've assumed `variable` is in `all_dependencies`;
                    # before calling this function all variable not in
                    # the dictionary should be added to the `determined`
                    # set.
                    for dependency in dependencies[variable]:
                        decisions = dependency | decide(  determined
                                                        | dependency
                                                        | {variable})
                        if len(decisions) < len(best_decisions):
                            best_decisions = decisions
                return best_decisions
            decisions = {v  for v in variables if v not in dependencies}
            return decisions | decide(decisions.copy())
        def get_literal_info(literal: Literal):
            variables = get_variables(literal)
            influential = sorted(influential_rank[v] for v in variables)
            appearance = sorted(appearance_rank[v] for v in variables)
            new_decisions = get_decision(literal)
            negative_weight = (    len(new_decisions)
                               and isinstance(literal, NegatedAtom))
            return (negative_weight,
                    len(new_decisions),
                    appearance,
                    influential)
        def select_condition(condition: Literal):
            time = len(result) - 1
            for variable in get_variables(condition):
                appearance_rank[variable] = min(time,
                                                appearance_rank[variable])
            conditions.remove(condition)
            result[-1].add_precondition(Condition(condition))

        while conditions:
            result.append(MicroAction())
            current_decisions = set()
            new_decisions = set()
            current_size = 0
            new_size = 0
            selected = None
            while (    (   len(new_decisions) <= len(current_decisions)
                        or not current_decisions)
                   and (   new_size < max(current_size, size_threshold)
                        or not current_size)):
                current_decisions = new_decisions
                current_size = new_size
                if selected is not None:
                    select_condition(selected)
                best = ((float('inf'), [float('inf')], [float('inf')]), None)
                for condition in conditions:
                    if (    result[-1].args
                        and result[-1].args.isdisjoint(get_args(condition))):
                        continue
                    key = get_literal_info(condition)
                    if key < best[0]:
                        best = (key, condition)
                if best[1] is None:
                    # Can't find any suitable condition
                    break
                new_decisions = get_decision(best[1])
                new_args = result[-1].args.union(get_variables(best[1]))
                selected = best[1]
                new_size = self.__count_estimate(new_args,
                                                   result[-1].preconditions
                                                 | {Condition(selected)})
        return result

    def __prepare_transitions(self,
                              partial_state: Set[Condition],
                              transitions: List[Transition]) -> List[MicroAction]:
        """Prepares the ordered micro-action list of transitions

        To complete the actions' definition, we need to specify its
        transitions. Here, we try to complete -as much as possible- the
        related information needed by each transition. It is also
        important to consider the possibility that a transition affect
        other transition's condition. This relation might even be cyclic.
        For example, one transition might affect the condition of another
        one, and that one might affect the first one's condition. Here,
        we find those transitions and merge them.
        Finally the ordered list of completed transitions will be
        returned as a list of micro-actions.

        Returns:
            List[MicroAction]: Ordered transitions
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
        statics = {c
                   for c in partial_state
                   if self.__knowledge.is_static(c.condition.predicate)}
        for transition in transitions:
            transition = self.__complete_transition(transition, statics)
        return transitions

    def __order_micro_actions(self,
                              preconditions: List[MicroAction],
                              transitions: List[MicroAction]):
        for id, micro_action in enumerate(preconditions + transitions):
            micro_action.id = id
        ids = [m.id for m in preconditions + transitions]

        def prepare_graph() -> Graph[MicroAction]:
            graph = Graph(preconditions + transitions)
            
            # Add edges for the precondition vertices.
            # NOTE: We have assumed the order of preconditions specifies
            #       the order of determining the arguments.
            determined: Dict[str, MicroAction] = {}
            for micro_action in preconditions + transitions:
                for arg in micro_action.args:
                    if arg in determined:
                        graph.add_edge((determined[arg], micro_action))
                    elif micro_action in preconditions:
                        determined[arg] = micro_action
            distinct_args = self.__distinct_args
            for transition in transitions:
                for other in (preconditions + transitions):
                    if other == transition:
                        continue
                    if other.is_threatened_by(transition, distinct_args):
                        graph.add_edge((other, transition))
            return graph

        def get_micro_action_by_id(micro_actions: List[MicroAction], id):
            for micro_action in micro_actions:
                if id == micro_action.id:
                    return micro_action
            return None

        def merge(graph: Graph[MicroAction], pervious, next):
            graph = deepcopy(graph)
            previous = get_micro_action_by_id(graph.vertices, pervious.id)
            next = get_micro_action_by_id(graph.vertices, next.id)
            next.merge(previous)
            graph.merge(next, previous)
            return graph

        def are_mergeable(graph, pervious, next):
            if (    not pervious.args.issuperset(next.args)
                and not next.args.issuperset(pervious.args)):
                return False
            return not graph.is_merging_make_a_cycle(pervious, next)

        def evaluation(graph: Graph[MicroAction]):
            preconditions = 0
            for vertex in graph.vertices:
                preconditions += 1 if vertex.has_precondition else 0
            return (preconditions, len(graph.vertices))

        def beam_search(width: int, graph: Graph[MicroAction]): 
            candidates: List[Graph[MicroAction]] = [graph]
            for id in ids:
                i = 0
                while i < len(candidates):
                    graph = candidates[i]
                    i += 1
                    current = get_micro_action_by_id(graph.vertices, id)
                    if current is None:
                        continue
                    for vertex in graph.vertices:
                        if id <= vertex.id:
                            continue
                        if are_mergeable(graph, vertex, current):
                            candidates.append(merge(graph, vertex, current))
                candidates = sorted(candidates, key=evaluation)[:width]
            return candidates[0]

        graph = prepare_graph()
        graph = beam_search(BEAM_SEARCH_WIDTH, graph)

        def priority(micro_action: MicroAction) -> List[int]:
            # Micro action with more precondition should be
            # placed earlier.
            return (  [2] * len(micro_action.preconditions)
                    + [1] * len(micro_action.transitions))
        return graph.topological_order(vertex_priority=priority)

    def __merge_micro_actions(self,
                              micro_actions: List[MicroAction],
                              size_threshold:int):
        def should_be_merged(action1: MicroAction, action2: MicroAction):
            if len(action1.args) < len(action2.args):
                return should_be_merged(action2, action1)
            if action1.args.issuperset(action2.args):
                return True
            if action1.args.isdisjoint(action2.args) or not size_threshold:
                return False
            conditions = action1.preconditions.union(action2.preconditions)
            estimate1 = self.__count_estimate(action1.args,
                                              action1.preconditions)
            estimate2 = self.__count_estimate(action2.args,
                                              action2.preconditions)
            args = action1.args.union(action2.args)
            estimate = self.__count_estimate(args, conditions)
            return estimate <= max(size_threshold, estimate1 + estimate2)

        processed = [micro_actions[0]]
        for micro_action in micro_actions[1:]:
            while processed and should_be_merged(processed[-1], micro_action):
                micro_action.merge(processed[-1])
                del processed[-1]
            processed.append(micro_action)
        return processed

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

    def __complete_transition(self,
                              transition: MicroAction,
                              conditions: Iterable[Condition]) -> MicroAction:
        """Add related conditions to the given Transition

        Find transition's related conditions and add them to it. Related
        conditions are
        1. static conditions overlapped with transition's
           arguments, 
        2. conditions with the arguments which are the subset
           of the transition's arguments.
        """
        conditions = conditions.copy()
        level_off = False
        while not level_off:
            level_off = True
            for condition in conditions:
                args = condition.find_args()
                name = condition.condition.predicate
                if (transition.args.issuperset(args)
                    or ((not transition.args.isdisjoint(args))
                        and self.__knowledge.is_static(name))):
                    transition.merge(MicroAction().add_precondition(condition))
                    conditions.remove(condition)
                    level_off = False
                    break
        return transition

    def __complete_micro_actions(self,
                                 micro_actions: List[MicroAction],
                                 partial_state: Iterable[Condition]):
        partial_state = partial_state.copy()
        for micro_action in micro_actions:
            for condition in partial_state:
                if micro_action.args.issuperset(condition.find_args()):
                    micro_action.add_precondition(condition)
            partial_state = (micro_action
                             .update_partial_state(partial_state,
                                                   self.__distinct_args))
        return micro_actions

    def __count_estimate(self, args, conditions: Iterable[Condition]):
        args = [a for a in self.__args if a.name in args]
        conditions = [c.condition for c in conditions]
        return self.__knowledge.count_estimate(args, conditions)

    def __find_distinct_args(self, preconditions: List[Literal]):
        distinct_args = {a.name: [] for a in self.__args}
        def get_name(arg):
            return arg.name if isinstance(arg, TypedObject) else arg
        for precondition in preconditions:
            if not isinstance(precondition, NegatedAtom):
                continue
            if precondition.predicate != "=":
                continue
            name1 = get_name(precondition.args[0])
            name2 = get_name(precondition.args[1])
            if name1 in distinct_args and name2 in distinct_args:
                distinct_args[name1].append(name2)
                distinct_args[name2].append(name1)

        for arg1, arg2 in combinations(self.__args, 2):
            type1, type2 = (arg1.type_name, arg2.type_name)
            if not self.__knowledge.has_shared_elements(type1, type2):
                distinct_args[arg1.name].append(arg2.name)
                distinct_args[arg2.name].append(arg1.name)
        return distinct_args