from typing import Iterable, List, Set
from itertools import chain, permutations
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
        self.__args = {p.name: p.type_name for p in action.parameters}
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
        influential_order = self.__order_variables(parameters, preconditions)
        conditions = self.__order_conditions(preconditions, influential_order)
        conditions = [Condition(c) for c in conditions]
        conditions = [MicroAction().add_precondition(c) for c in conditions]
        conditions = self.__merge_micro_actions(conditions, size_threshold)
        transitions = self.__get_transitions(action.effects)
        preconditions = {Condition(p) for p in preconditions}
        transitions = self.__prepare_transitions(preconditions,
                                                 transitions,
                                                 size_threshold)
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
                # print("WARNING: Not all variables are covered by:", effect)
                # print("         We fix it by adding a (redundant) transition")
                transitions.append(Transition(conditions, effect, set()))
        return transitions

    def __order_variables(self, variables: List[str], conditions) -> List[str]:
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

    @staticmethod
    def __order_conditions(conditions: List[Literal], ordered_variables):
        appearance_rank = {variable: float('inf')
                           for variable in ordered_variables}
        influential_rank = {variable: i
                            for i, variable in enumerate(ordered_variables)}
        def get_ranking(condition):
            ranking = [(appearance_rank[arg], influential_rank[arg])
                       for arg in condition.args if arg.startswith("?")]
            ranking.sort()
            return ranking
        size = len(conditions)
        for i in range(size):
            best_ranking = get_ranking(conditions[i])
            for j in range(i + 1, size):
                ranking = get_ranking(conditions[j])
                if ranking < best_ranking:
                    best_ranking = ranking
                    conditions[i], conditions[j] = conditions[j], conditions[i]
            appearance_rank.update({arg: min(i, appearance_rank[arg])
                                    for arg in conditions[i].args
                                    if arg.startswith("?")})
        return conditions

    def __prepare_transitions(self,
                              partial_state: Set[Condition],
                              transitions: List[Transition],
                              size_threshold: int) -> List[MicroAction]:
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
            if transition1.is_threatened_by(transition2):
                graph[transition1].append(transition2)

        components = get_sccs_adjacency_dict(graph)
   
        transitions = [reduce(lambda micro_action, transition:
                                 micro_action.add_transition(transition),
                              component,
                              MicroAction())
                       for component in components]
        for transition in transitions:
            transition = self.__complete_transition(transition,
                                                    partial_state,
                                                    size_threshold)
            partial_state = transition.update_partial_state(partial_state)
        return transitions

    @staticmethod
    def __order_micro_actions(preconditions: List[MicroAction],
                              transitions: List[MicroAction]):
        graph = Graph(preconditions + transitions)
        # Adding preconditions' order
        graph = reduce(Graph.add_edge,
                       zip(preconditions, preconditions[1:]),
                       graph)
        # Adding transitions' order
        graph = reduce(Graph.add_edge,
                       zip(transitions, transitions[1:]),
                       graph)
        
        # Postponing the modification of state variables until the point
        # we need their old values.
        graph = reduce(Graph.add_edge,
                       ((source, destination)
                        for source in preconditions
                        for destination in transitions
                        if source.is_threatened_by(destination)),
                       graph)

        # Performing the transitions after all their arguments have been fixed.
        first_variable_appearance = {}
        for index, precondition in enumerate(preconditions):
            for arg in precondition.args:
                if arg not in first_variable_appearance:
                    first_variable_appearance[arg] = index
        for transition in transitions:
            last_index = -1
            for arg in transition.args:
                index = first_variable_appearance.get(arg, -1)
                last_index = max(last_index, index)
            if last_index != -1:
                graph.add_edge((preconditions[last_index], transition))

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
            args = action1.args.union(action2.args)
            estimate = self.__count_estimate(args, conditions)
            return estimate < size_threshold

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
        shared_arguments = {arg: [] for arg in self.__args}
        argument_predicate = lambda argument: f"{self.__name}_{argument[1:]}"
        for micro_action in self.__micro_actions:
            for arg in micro_action.args:
                shared_arguments[arg].append(micro_action)
        for arg, shared_micro_actions in shared_arguments.items():
            if len(shared_micro_actions) < 2:
                continue
            arg_type = self.__args[arg]
            self.__new_predicates.append((argument_predicate(arg),
                                          [TypedObject(arg, arg_type)],
                                          [default_values[arg_type]]))
            use_predicate((argument_predicate(arg), (default_values[arg_type],)),
                          shared_micro_actions[-1],
                          [shared_micro_actions[0]])
            use_predicate((argument_predicate(arg), (arg,)),
                          shared_micro_actions[0], shared_micro_actions[1:])

        return self

    def __complete_transition(self,
                              transition: MicroAction,
                              conditions: Iterable[Condition],
                              size_threshold: int) -> MicroAction:
        """Add related conditions to the given Transition

        Find transition's related conditions and add them to it as much
        as the upper-bound estimate of the of grounded actions count for
        the transition is less than the given threshold.
        """

        conditions = [MicroAction().add_precondition(c) for c in conditions]
        added_conditions = set()
        args = transition.args

        level_off = False
        while not level_off:
            level_off = True
            best = (float('inf'), None, None)
            for condition in conditions:
                if args.isdisjoint(condition.args):
                    continue
                if args.issuperset(condition.args):
                    best = (0, condition)
                    break
                new_candidate = added_conditions.union(condition.preconditions)
                estimate = self.__count_estimate(args.union(condition.args),
                                                 new_candidate)
                if estimate < best[0]:
                    best = (estimate, condition)
            if (   best[0] < size_threshold
                or best[0] <= self.__count_estimate(args, added_conditions)):
                transition = transition.merge(best[1])
                added_conditions.update(best[1].preconditions)
                level_off = False
                conditions.remove(best[1])
                args.update(best[1].args)
        return transition
    
    def __count_estimate(self, args, conditions: Iterable[Condition]):
        args = [TypedObject(arg, self.__args[arg]) for arg in args]
        conditions = [c.condition for c in conditions]
        return self.__knowledge.count_estimate(args, conditions)