#! /usr/bin/env python3


from typing import List, Dict, Set, Tuple, Iterable
from itertools import chain
from functools import reduce

import normalize
import pddl_parser
from invariant_finder import find_invariants
from invariants import Invariant
import pddl
from pddl.tasks import Task
from pddl.actions import Action
from pddl.effects import ConditionalEffect, Effect, SimpleEffect
from pddl.conditions import Conjunction, Literal, Atom, NegatedAtom, Truth


Predicate = Tuple[str, Iterable[str]]  # predicate type


class AtomicActionPart:
    def find_args(self):
        raise NotImplementedError

    @staticmethod
    def _find_args_in_literal(literal: Literal):
        return {arg for arg in literal.args if arg[0] == "?"}


class Condition(AtomicActionPart):
    def __init__(self, condition: Literal):
        self.__condition = condition

    def __str__(self):
        return str(self.__condition)

    def find_args(self):
        if isinstance(self.__condition, Literal):
            return self._find_args_in_literal(self.__condition)
        raise NotImplementedError("Other Conditions are not supported!")

    def dump(self, indent: str):
        print(f"{indent}{str(self.__condition)}")


class Transition(AtomicActionPart):
    def __init__(self,
                 conditions: List[Literal],
                 main_effect: Literal,
                 variables_ids: Set[int]):
        self.__main_effect = main_effect
        self.__conditions = conditions
        self.__variables_ids = variables_ids
        self.__effects = [main_effect]

    def check_delete_effect(self, variables_ids, conditions, del_effect):
        """Updates the transition according to the given delete effect

        Checks if the given delete effect is related to this transition
        or not; if it affects the same state variable as the transition,
        and its condition is logical consequence of the transition's
        conditions, then the delete effect is related to this transition.

        Returns:
            Set[int]: The set of IDs of common state variables
        """
        common_variables_ids = self.__variables_ids.intersection(variables_ids)
        if not common_variables_ids:
            # <del_effect> is not related to this transition
            return set()

        statements = set().union(*self.__conditions,
                                 {self.__main_effect.negate()},
                                 {del_effect.negate()})
        # TODO: We are supposed to check if <condition> is a logical
        #       consequence of <statement> or not. In the following,
        #       for simplicity, I have not used some other knowledge in
        #       action's precondition, the problem itself, or even the
        #       possible unification, so it might be not precise. I
        #       should fix this!
        if statements.issuperset(set(conditions)):
            self.__effects.append(del_effect)
            return common_variables_ids

        return set()

    def dump(self, indent: str):
        conditions = [str(condition) for condition in self.__conditions]
        print(f"{indent}{' and '.join(conditions)}:")
        for effect in self.__effects:
            print(f"{indent}\t{str(effect)}")

    def find_args(self):
        args = set().union(*[self._find_args_in_literal(condition)
                             for condition in self.__conditions])
        args = args.union(*[self._find_args_in_literal(effect)
                            for effect in self.__effects])
        return args


class MicroAction:
    def __init__(self, main_action_name):
        self.__main_name = main_action_name
        self.__preconditions: List[Condition] = []
        self.__transitions: List[Transition] = []

    def add_precondition(self, condition: Condition):
        self.__preconditions.append(condition)
        return self

    def add_transition(self, transition: Transition):
        self.__transitions.append(transition)
        return self

    def dump(self, name_postfix: str, indent: str):
        print(f"{indent}Micro-Action: {self.__main_name}{name_postfix}")
        indent += "\t"
        print(f"{indent}Conditions:")
        for condition in self.__preconditions:
            condition.dump(indent + "\t")
        print(f"{indent}Transitions:")
        for transition in self.__transitions:
            transition.dump(indent + "\t")


class Knowledge:
    """Extracts and provide predicates' knowledge

    For some predicates, we can partition their arguments to the
    "counted variable" and the other "parameters". By, this
    partitioning, we can uniquely determine the value of the
    "counted variable" argument, when we are given the values for the
    other "parameters", in each possible state.

    Additionally, it finds state variable of the given problem, and
    determines each predicate belongs to which state variables.

    This class extracts and provides these kinds of knowledge.
    """

    def __init__(self, task: Task):
        self.__omitted_positions = dict()  # A dictionary from predicates to
                                           # the list of their <omitted_pos>s
                                           # (or, the positions of their
                                           # <counted variable>s).
        self.__variables = dict()  # predicate -> Set[variable-id],
                                   # it shows each predicate participate
                                   # in which state variables.
        self.__extract_knowledge(task)

    def get_relations(self, predicate: Predicate) -> List[Tuple[str, str]]:
        relations = []
        for omitted_position in self.__omitted_positions.get(predicate[0], []):
            counted_variable = predicate[1][omitted_position]
            for arg in predicate[1]:
                if arg == counted_variable:
                    continue
                relations.append((arg, counted_variable))
        return relations

    def get_variables(self, literal: Literal):
        return self.__variables.get(literal.predicate, set()).copy()

    def __extract_knowledge(self, task: Task):
        normalize.normalize(task)
        invariants = find_invariants(task, None)
        invariant_size = self.__exactly_one_invariants(invariants, task.init)
        for invariant in invariant_size:
            for part in invariant.parts:
                if part.omitted_pos != -1:
                    (self
                     .__omitted_positions
                     .setdefault(part.predicate, [])
                     .append(part.omitted_pos))

        state_variables = self.__find_state_variables(invariant_size)
        for variable_id, invariant in enumerate(state_variables):
            for predicate in invariant.predicates:
                self.__variables.setdefault(predicate, set()).add(variable_id)

    @staticmethod
    def __exactly_one_invariants(invariants, initial_state):
        """Finds invariants with weight one and returns their sizes

        First filters out every invariants with weight not equal to one,
        and then returns the sizes of the remaining invariants (the
        number of all possible indices, in our "array" analogy).

        Returns:
            Dict[Invariant, int]: Maps Invariants to their sizes
        """

        # NOTE: The following code is similar to the <useful_groups()>
        #       function, but with slight modifications, to keep the
        #       invariants lifted, and also returns the number of
        #       possible groups(grounded versions) of each invariants.
        predicate_to_invariants = dict()
        for invariant in invariants:
            for predicate in invariant.predicates:
                (predicate_to_invariants
                 .setdefault(predicate, [])
                 .append(invariant))

        nonempty_groups = set()
        overcrowded_groups = set()
        for atom in initial_state:
            if isinstance(atom, pddl.Assign):
                continue
            for invariant in predicate_to_invariants.get(atom.predicate, []):
                group_key = (invariant, tuple(invariant.get_parameters(atom)))
                if group_key not in nonempty_groups:
                    nonempty_groups.add(group_key)
                else:
                    overcrowded_groups.add(group_key)
        useful_groups = nonempty_groups - overcrowded_groups
        invariant_size = dict()
        for (invariant, _) in useful_groups:
            invariant_size[invariant] = invariant_size.get(invariant, 0) + 1
        return invariant_size

    @staticmethod
    def __find_state_variables(invariant_size: Dict[Invariant, int]):
        memoized_value = {frozenset(): ([], 0)}  # predicates -> best value
        def __find_minimum_state_variables(predicates):
            # NOTE: Finding minimum state variable is done by using
            #       exhaustive search with memoization technique. I
            #       believe the number of possible state variables isn't
            #       too much; if my assumption is not correct, then our
            #       memory consumption and runtime will be overwhelming.
            predicates = frozenset(predicates)
            if predicates in memoized_value:
                return memoized_value[predicates]
            memoized_value[predicates] = ([], float('inf'))
            (selected_state_variables, minimum_number) = ([], float('inf'))
            for invariant in invariant_size:
                if predicates.isdisjoint(invariant.predicates):
                    continue
                remaining_predicates = predicates - invariant.predicates
                (state_variables, number) =\
                    __find_minimum_state_variables(remaining_predicates)
                number += invariant_size[invariant]
                if number < minimum_number:
                    minimum_number = number
                    selected_state_variables = state_variables + [invariant]
            result = (selected_state_variables, minimum_number)
            memoized_value[predicates] = result
            return result

        predicates = set()
        for invariant in invariant_size:
            for predicate in invariant.predicates:
                predicates.add(predicate)

        (state_variables, _) = __find_minimum_state_variables(predicates)
        return state_variables


class Graph:
    """Directed graph (representing the influential relation)

    Maintains the influential relation among variables. In other words,
    the graph has an edge (u, v) if and only if the variable u has an
    influence on
    variable v (or, variable v depends on variable u).

    Additionally, this class produces a topological order of the
    vertices.
    """
    Vertex = str  # Vertex type

    def __init__(self, vertices: List[Vertex] = []):
        self.__graph = {vertex: [] for vertex in vertices}

    def __str__(self) -> str:
        return str(self.__graph)
    
    def add_edge(self, edge: Tuple[Vertex, Vertex]) -> 'Graph':
        source, destination = edge
        self.__graph.setdefault(source, []).append(destination)
        return self

    def topological_order(self) -> List[Vertex]:
        def dfs(vertex, visited, order):
            visited.append(vertex)
            for destination in self.__graph[vertex]:
                if destination in visited:
                    continue
                visited, order = dfs(destination, visited, order)
            return visited, [vertex] + order

        order = []
        visited = []
        for vertex in self.__graph:
            if vertex not in order:
                visited, order = dfs(vertex, visited, order)

        return order


class ActionSplitter:
    """Decomposes each action into a series of micro-actions"""

    def __init__(self, knowledge: Knowledge):
        self.__knowledge = knowledge

    def split_action(self, action: Action) -> List[MicroAction]:
        conditions = self.__get_conditions(action.precondition)
        parameters = [parameter.name for parameter in action.parameters]
        influential_order = self.__order_variables(parameters, conditions)
        conditions = self.__order_conditions(conditions, influential_order)
        transitions = self.__get_transitions(action.effects)
        micro_action = MicroAction(action.name)
        for transition in transitions:
            micro_action.add_transition(transition)

    @staticmethod
    def __get_conditions(condition):
        if isinstance(condition, Conjunction):
            return list(chain(*[ActionSplitter.__get_conditions(part)
                                for part in condition.parts]))
        if isinstance(condition, Literal):
            return [condition]
        if isinstance(condition, Truth):
            return []
        raise ValueError("Unexpected condition type!")

    def __get_transitions(self, raw_effects):
        effects = []
        for effect in raw_effects:
            if isinstance(effect, SimpleEffect):
                effects.append(([], effect.effect))
            elif isinstance(effect, ConditionalEffect):
                conditions = self.__get_conditions(effect.condition)
                effects.append((conditions, effect.effect))
            elif isinstance(effect, Effect):
                conditions = self.__get_conditions(effect.condition)
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
                print("WARNING: Not all variables are covered by:", effect)
                print("         We fix it by adding a (redundant) transition")
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
                                    for arg in conditions[i].args})
        return conditions


if __name__ == "__main__":
    print("Parsing...")
    task = pddl_parser.open()
    print("Extract knowledge...")
    knowledge = Knowledge(task)
    splitter = ActionSplitter(knowledge)
    print("Splitting actions ...")
    for action in task.actions:
        splitter.split_action(action)