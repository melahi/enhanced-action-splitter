from typing import Iterable, List, Tuple, Dict
from itertools import product, chain

import pandas as pd

import normalize
from invariant_finder import find_invariants
from invariants import Invariant
from pddl import Task, Literal, Assign, Effect
from pddl.conditions import ConstantCondition, JunctorCondition
from pddl.pddl_types import TypedObject

from .common import Predicate


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
                                           # the list of their `omitted_pos`s
                                           # (or, the positions of their
                                           # `counted variable`s).
        self.__variables = dict()  # predicate -> Set[variable-id],
                                   # it shows each predicate participate
                                   # in which state variables.

        self.__objects: Dict[str, list] = dict() # type -> List of objects

        self.__statics: Dict[str, pd.DataFrame] = dict() # Static relations

        self.__set_statics(task)
        self.__set_static_function()
        self.__extract_knowledge(task)
        self.__eliminate_universal_quantifier_effects(task)

    @property
    def default_objects(self):
        return {t: self.__objects[t][0] for t in self.__objects}

    def get_relations(self, predicate: Predicate) -> List[Tuple[str, str]]:
        is_constant = lambda arg: not str(arg).startswith("?")
        relations = []
        for omitted_position in self.__omitted_positions.get(predicate[0], []):
            counted_variable = predicate[1][omitted_position]
            if is_constant(counted_variable):
                continue
            for arg in predicate[1]:
                if arg == counted_variable or is_constant(arg):
                    continue
                relations.append((arg, counted_variable))
        return relations

    def get_variables(self, literal: Literal):
        return self.__variables.get(literal.predicate, set()).copy()

    def count_estimate(self,
                       args: List[TypedObject],
                       conditions: Iterable[Literal]) -> int:
        """ Calculates an upper-bound estimate for possible instantiations

        Exploiting the static knowledge of the domain, this function
        finds a virtually tight upper-bound for the number of possible
        instantiations of the `args`, based on the given `conditions`.
        """
        covered_args = []
        static_relations = []
        for condition in conditions:
            relation = self.__statics.get(condition.predicate, None)
            if relation is None:
                continue
            condition_args = [a.name if isinstance(a, TypedObject) else a
                              for a in condition.args]
            covered_args.extend(condition_args)
            relation = relation.copy(deep=False)
            relation.columns = condition_args
            constant_args = {a: a
                             for a in condition_args if not a.startswith("?")}
            if constant_args:
                relation = relation.merge(constant_args)
            static_relations.append(relation)
        estimate_count = self.__join_result_count(static_relations)
        for arg in args:
            if arg.name in covered_args:
                continue
            estimate_count *= len(self.__objects[arg.type_name])
        return estimate_count

    def __extract_knowledge(self, task: Task):
        normalize.normalize(task)
        self.__extract_domains(task)
        task = self.__filter_not_instantiable_actions(task)
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

        # NOTE: The following code is similar to the `useful_groups()`
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
            if isinstance(atom, Assign):
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

    def __filter_not_instantiable_actions(self, task: Task):
        actions = []
        for action in task.actions:
            for parameter in action.parameters:
                if parameter.type_name not in self.__objects:
                    break
            else:
                actions.append(action)
        task.actions = actions
        return task

    def __extract_domains(self, task: Task):
        objects = self.__objects
        parents = {t.name: t.basetype_name for t in task.types}
        for obj in task.objects:
            type_name = obj.type_name
            while type_name:
                objects.setdefault(type_name, []).append(obj)
                type_name = parents.get(type_name, None)

    def __eliminate_universal_quantifier_effects(self, task: Task):
        def instantiate(condition, mapping):
            if isinstance(condition, ConstantCondition):
                return condition
            if isinstance(condition, Literal):
                return condition.rename_variables(mapping)
            if isinstance(condition, JunctorCondition):
                new_parts = [instantiate(p, mapping) for p in condition.parts]
                return condition.change_parts(new_parts)
            raise NotImplementedError("Not expected condition!")

        def eliminate(effect: Effect):
            assert isinstance(effect, Effect),  "Unexpected effect type!"
            mapping_keys = [p.name for p in effect.parameters]
            domains = [self.__objects[p.type_name] for p in effect.parameters]
            mappings = (dict(zip(mapping_keys, x)) for x in product(*domains))
            result = []
            for mapping in mappings:
                result.append(Effect([],
                                     instantiate(effect.condition, mapping),
                                     instantiate(effect.literal, mapping)))
            return result

        for action in task.actions:
            action.effects = [*chain(*(eliminate(e) for e in action.effects))]
        return task

    @staticmethod
    def __find_static_predicates(task: Task):
        dynamic_predicates = set(['='])  # Excluding '=' from static predicates
        for action in task.actions:
            for effect in action.effects:
                dynamic_predicates.add(effect.literal.predicate)
        return [p for p in task.predicates if p.name not in dynamic_predicates]

    def __set_statics(self, task: Task):
        statics = {s.name: [] for s in self.__find_static_predicates(task)}
        for initial_value in task.init:
            statics.get(initial_value.predicate, []).append(initial_value.args)
        self.__statics = {k: pd.DataFrame(v) for k, v in statics.items()}

    @staticmethod
    def __join_result_count(relations: List[pd.DataFrame]) -> int:
        # TODO: Use memoization to optimize this function
        def are_mergeable(relation1, relation2):
            return any(c in relation2.columns for c in relation1.columns)
        count = 1
        while relations:
            current_relation = relations.pop()
            while True:
                # A naive approach to join the relations, it can be improved!
                for i in range(len(relations)):
                    if are_mergeable(current_relation, relations[i]):
                        current_relation.merge(relations.pop(i))
                        break
                else:
                    break
            count *= current_relation.shape[0]
        return count

    def __set_static_function(self):
        """Sets static functions
        
        This function finds those static relations that can be
        considered as a function (assigns only one value to each index).
        Those functions then are appended to `self.__omitted_positions`
        and the omitted position will be the index position of the value.
        """
        for name, relation in self.__statics.items():
            if len(relation.columns) < 2:
                continue
            for i, column in enumerate(relation.columns):
                candidate = relation.drop(columns=[column]).drop_duplicates()
                if candidate.shape[0] == relation.shape[0]:
                    self.__omitted_positions.setdefault(name, []).append(i)
        return self