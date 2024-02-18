from typing import Iterable, List, Tuple, Dict, Set
from itertools import product, chain

import pandas as pd

import normalize
from invariant_finder import find_invariants
from invariants import Invariant
from .invariants import construct_arg_expert
import pddl
from pddl import Task, Action, Literal, Atom, Assign, Effect, NegatedAtom
from pddl.conditions import Conjunction, ConstantCondition
from pddl.conditions import JunctorCondition, Truth
from pddl.pddl_types import TypedObject

from .common import Predicate, get_conditions


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

        self.__type_parent: Dict[str, str] = dict() # Types' parent relation

        self.__arg_expert = construct_arg_expert(task)
        self.__memoized_max_count: Dict[Tuple[str, Tuple[int]], int] = {}

        self.__set_statics(task)
        self.__set_static_function()
        self.__extract_knowledge(task)
        self.__normalize(task)
        self.__set_hierarchy(task)

    @property
    def default_objects(self):
        return {t: self.__objects[t][0] for t in self.__objects}

    @property
    def arg_expert(self):
        return self.__arg_expert

    def is_static(self, predicate_name: str):
        return predicate_name in self.__statics

    def omittable_arguments(self, predicate: Predicate) -> List[str]:
        return [predicate[1][o]
                for o in self.__omitted_positions.get(predicate[0], [])]

    def get_relations(self, predicate: Predicate) -> List[Tuple[str, str]]:
        is_constant = lambda arg: not str(arg).startswith("?")
        relations = []
        omitted_positions = self.__omitted_positions.get(predicate[0], [])
        for omitted_position in omitted_positions:
            counted_variable = predicate[1][omitted_position]
            if is_constant(counted_variable):
                continue
            for i, arg in enumerate(predicate[1]):
                if i in omitted_positions or is_constant(arg):
                    continue
                relations.append((arg, counted_variable))
        return relations

    def get_variables(self, literal: Literal):
        return self.__variables.get(literal.predicate, set()).copy()

    def all_count_estimate(self,
                           args: List[TypedObject],
                           conditions: Iterable[Literal]) -> int:
        """ Calculates an upper-bound estimate for possible instantiations

        Exploiting the static knowledge of the domain, this function
        finds a virtually tight upper-bound for the number of possible
        instantiations of the `args`, based on the given `conditions`.

        Returns an integer considering all arguments in instantiations.

        NOTE: We do not support negative literals
        """
        count_estimate = self.__count_estimate_accurate(args, conditions)
        # count_estimate = self.__count_estimate_fast(args, conditions)
        return count_estimate

    def has_shared_elements(self, type1: str, type2: str) -> bool:
        def is_ancestor(subject, object):
            while object:
                if subject == object:
                    return True
                if self.__type_parent[object] == object:
                    object = None
                else:
                    object = self.__type_parent[object]
            return False

        return is_ancestor(type1, type2) or is_ancestor(type2, type1)

    def __get_positive(self, task: Task, negative: NegatedAtom):
        name = f"NOT-{negative.predicate}"
        positive = Atom(name, negative.args)
        if any(p.name == name for p in task.predicates):
            return positive
        negative_predicate = next(p
                                  for p in task.predicates
                                  if p.name == negative.predicate)
        new_predicate = pddl.Predicate(name, negative_predicate.arguments)
        task.predicates.append(new_predicate)

        args_types = [a.type_name for a in new_predicate.arguments]
        excluded_args = [a.args
                         for a in task.init
                         if    isinstance(a, Atom)
                           and a.predicate == negative.predicate]
        for possible_arg in product(*(self.__objects[t] for t in args_types)):
            possible_arg = tuple(a.name for a in possible_arg)
            if possible_arg in excluded_args:
                continue
            task.init.append(Atom(name, possible_arg))

        negated_class = {Atom: NegatedAtom, NegatedAtom: Atom}
        for action in task.actions:
            new_effects = []
            for effect in action.effects:
                assert isinstance(effect, Effect),  "Unexpected effect type!"
                if effect.literal.predicate == negative.predicate:
                    new_effect = effect.copy()
                    new_literal = negated_class[effect.literal.__class__](
                        name, effect.literal.args)
                    new_effect.literal = new_literal
                    new_effects.append(new_effect)
            action.effects.extend(new_effects)
        return positive

    def __get_rid_of_negative_preconditions(self, task: Task):
        for action in task.actions:
            conditions = get_conditions(action.precondition)
            for i, condition in enumerate(conditions):
                if isinstance(condition, NegatedAtom) and condition.predicate != "=":
                    conditions[i] = self.__get_positive(task, condition)
            action.precondition = Conjunction(conditions)
            for effect in action.effects:
                conditions = get_conditions(effect.condition)
                for i, condition in enumerate(conditions):
                    if isinstance(condition, NegatedAtom) and condition.predicate != "=":
                        conditions[i] = self.__get_positive(task, condition)
                effect.condition = Conjunction(conditions)
        conditions = get_conditions(task.goal)
        for i, condition in enumerate(conditions):
            if isinstance(condition, NegatedAtom) and condition.predicate != "=":
                conditions[i] = self.__get_positive(task, condition)
        task.goal = Conjunction(conditions)
        return task

    def __extract_knowledge(self, task: Task):
        normalize.normalize(task)
        self.__extract_domains(task)
        task = self.__filter_not_instantiable_actions(task)
        task = self.__get_rid_of_negative_preconditions(task)
        # TODO: Perhaps I can find `reachable_action_params` needed for the
        #       following function, by using our own versions of `invariants`.
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

    def __count_estimate_accurate(self,
                                  args: List[TypedObject],
                                  conditions: Iterable[Literal]
                                 ) -> Tuple[Dict, int]:
        # NOTE: We do not support negative literals
        condition = [c for c in conditions if isinstance(c, Atom)]
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
            constant_args = {a: [a]
                             for a in condition_args if not a.startswith("?")}
            if constant_args:
                relation = relation.merge(pd.DataFrame(constant_args))
            static_relations.append(relation)
        variables = [a.name for a in args]
        estimate_count = self.__join_result_count(static_relations, variables)
        for arg in args:
            if arg.name in covered_args:
                continue
            estimate_count *= len(self.__objects[arg.type_name])
        return estimate_count

    def __count_estimate_fast(self,
                         args: List[TypedObject],
                         conditions: Iterable[Literal]) -> int:
        # NOTE: We do not support negative literals
        condition = [c for c in conditions if isinstance(c, Atom)]
        estimate_count = 1
        unfixed_args = {a.name for a in args}
        for condition in conditions:
            if condition.predicate not in self.__statics:
                continue
            condition_args = [a.name if isinstance(a, TypedObject) else a
                              for a in condition.args]
            fixed_columns = [i
                             for i, a in enumerate(condition_args)
                             if a not in unfixed_args]
            estimate_count *= self.__estimate_max_count(condition.predicate,
                                                        fixed_columns)
            unfixed_args.difference_update(condition_args)
        for arg in args:
            if arg.name in unfixed_args:
                estimate_count *= len(self.__objects[arg.type_name])
        return estimate_count

    def __estimate_max_count(self,
                             static_predicate: str,
                             fixed_columns: List[int]) -> int:
        fixed_columns = sorted(fixed_columns)
        key = (static_predicate, tuple(fixed_columns))
        if key in self.__memoized_max_count:
            return self.__memoized_max_count[key]
        all_possibilities = dict()
        not_fixed_columns = [i
                             for i in self.__statics[static_predicate].columns
                             if i not in fixed_columns]
        for row in self.__statics[static_predicate].values:
            (all_possibilities
             .setdefault(tuple(row[i] for i in fixed_columns), set())
             .add(tuple(row[i] for i in not_fixed_columns)))
        estimate_max_count = 0
        for possibilities in all_possibilities.values():
            estimate_max_count = max(estimate_max_count, len(possibilities))
        return self.__memoized_max_count.setdefault(key, estimate_max_count)

    def __filter_not_instantiable_actions(self, task: Task):
        actions = []
        for action in task.actions:
            for parameter in action.parameters:
                if parameter.type_name not in self.__objects:
                    break
            else:
                for condition in get_conditions(action.precondition):
                    if (    isinstance(condition, Atom)
                        and condition.predicate in self.__statics
                        and not self.__statics[condition.predicate].shape[0]):
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

    def __normalize(self, task: Task) -> Task:
        new_actions = []
        for action in task.actions:
            action = self.__move_single_condition_to_precondition(action)
            if action is not None:
                new_actions.append(action)
        task.actions = new_actions
        return self.__eliminate_universal_quantifier_effects(task)

    @staticmethod
    def __move_single_condition_to_precondition(action):
        if len(action.effects) == 0:
            return None
        condition = action.effects[0].condition
        if isinstance(condition, Truth):
            return action
        for effect in action.effects[1:]:
            if effect.condition != condition:
                return action
        action.precondition = (Conjunction([action.precondition, condition])
                               .simplified())
        for effect in action.effects:
            effect.condition = Truth()
        return action

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
            if (    isinstance(initial_value, Atom)
                and initial_value.predicate in statics):
                statics[initial_value.predicate].append(initial_value.args)
        self.__statics = {k: pd.DataFrame(v) for k, v in statics.items()}

    @staticmethod
    def __join_result_count(relations: List[pd.DataFrame],
                            variables: List[str]) -> int:
        # TODO: Use memoization to optimize this function
        def are_mergeable(relation1, relation2):
            return not set(relation1.columns).isdisjoint(relation2.columns)
        count = 1
        while relations:
            current = relations.pop()
            while True:
                # A naive approach to join the relations, it can be improved!
                for i in range(len(relations)):
                    if are_mergeable(current, relations[i]):
                        current = current.merge(relations.pop(i))
                        break
                else:
                    break
            if set(current.columns).issubset(variables):
                count *= current.shape[0]
                continue
            fixed = [c for c in current.columns if c not in variables]
            count *= max(current[fixed].value_counts())
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

    def __set_hierarchy(self, task: Task):
        root_type_name = None
        all_types = set()
        for pddl_type in task.types:
            if pddl_type.basetype_name is None:
                root_type_name = pddl_type.name
            self.__type_parent[pddl_type.name] = pddl_type.basetype_name
            all_types.add(pddl_type.name)
            all_types.add(pddl_type.basetype_name)
        for type_ in all_types:
            if type_ not in self.__type_parent:
                self.__type_parent[type_] = root_type_name
