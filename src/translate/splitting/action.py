from typing import Dict, Iterable, List, Set
from itertools import chain, combinations, permutations
from functools import reduce

from sccs import get_sccs_adjacency_dict
import pddl
from pddl import SimpleEffect, ConditionalEffect, Effect, Atom, NegatedAtom
from pddl import Literal, TypedObject

from .common import get_conditions
from .knowledge import Knowledge
from .micro_action import Condition, Transition, MicroAction
from .graph import Graph


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
        micro_actions = conditions + transitions
        micro_actions = self.__order_micro_actions(conditions, transitions)
        micro_actions = self.__merge_micro_actions(micro_actions, 0)
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
        variable_rank = {v: i for i, v in enumerate(influential_order)}
        def literal_rank(literal: Literal):
            rank = [variable_rank[v] for v in get_variables(literal)]
            rank.sort()
            return rank

        result: List[MicroAction] = []
        conditions = sorted(conditions, key=literal_rank)
        determined_variables = set()
        dependencies: Dict[str, List[Set[str]]] = {}
        for condition in conditions:
            if not isinstance(condition, Atom):
                continue
            predicate = (condition.predicate, get_args(condition))
            variables = set(get_variables(condition))
            for arg in self.__knowledge.omittable_arguments(predicate):
                dependency = variables - {arg}
                if arg in variables and dependency:
                    dependencies.setdefault(arg, []).append(dependency)
        def select_condition(condition: Literal):
            determined_variables.update(get_variables(condition))
            for variable in list(dependencies.keys()):
                if variable in determined_variables:
                    del dependencies[variable]
                    continue
                for dependency in dependencies[variable]:
                    if determined_variables.issuperset(dependency):
                        determined_variables.add(variable)
                        del dependencies[variable]
                        break
            conditions.remove(condition)
            result[-1].add_precondition(Condition(condition))

        while conditions:
            result.append(MicroAction())
            for condition in conditions:
                if determined_variables.issuperset(get_variables(condition)):
                    selected = condition
                    break
            else:
                selected = conditions[0]
            while selected is not None:
                select_condition(selected)
                for condition in conditions:
                    condition_vars = get_variables(condition)
                    vars = result[-1].args.union(condition_vars)
                    if (    (  self.__count_estimate(vars, [])
                             < size_threshold)
                        and determined_variables.issuperset(condition_vars)):
                        selected = condition
                        break
                else:
                    selected = None
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
        graph = Graph(preconditions + transitions)
        # Adding preconditions' order
        graph = reduce(Graph.add_edge,
                       zip(preconditions, preconditions[1:]),
                       graph)
        # Adding transitions' order
        graph = reduce(Graph.add_edge,
                       [(t1, t2)
                        for t1, t2 in permutations(transitions, 2)
                        if t1.is_threatened_by(t2, self.__distinct_args)],
                       graph)

        # Postponing the modification of state variables until the point
        # we need their old values, and all of their arguments have been
        # fixed.
        for transition in transitions:
            for precondition in reversed(preconditions):
                if (   precondition.is_threatened_by(transition,
                                                     self.__distinct_args)
                    or not precondition.args.isdisjoint(transition.args)):
                    graph.add_edge((precondition, transition))
                    break

        def priority(micro_action: MicroAction) -> List[int]:
            return (  [2] * len(micro_action.transitions)
                    + [1] * len(micro_action.preconditions))
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