import copy
from typing import List, Set, Dict, Optional

from pddl.conditions import Literal
from pddl.pddl_types import TypedObject

from .common import literal_to_string
from .invariants import ArgExpert

class AtomicActionPart:
    def __str__(self):
        return self.to_string(indent="")

    def find_args(self) -> Set[str]:
        raise NotImplementedError

    def is_threatened_by(self,
                         transition: 'Transition',
                         distinct_args: Dict[str, Set[str]]) -> bool:
        raise NotImplementedError

    def to_string(self, indent) -> str:
        raise NotImplementedError

    @staticmethod
    def _find_args_in_literal(literal: Literal) -> Set[str]:
        args = [a.name if isinstance(a, TypedObject) else a
                for a in literal.args]
        return {a for a in args if a.startswith("?")}

    @staticmethod
    def _are_possibly_the_same(literal1: Literal,
                               literal2: Literal,
                               distinct_args: Dict[str, Set[str]]) -> bool:
        if literal1.predicate != literal2.predicate:
            return False
        args1 = tuple(a.name if isinstance(a, TypedObject) else a
                      for a in literal1.args)
        args2 = tuple(a.name if isinstance(a, TypedObject) else a
                      for a in literal2.args)
        if args1 == args2:
            return True
        for arg1, arg2 in zip(args1, args2):
            if arg2 in distinct_args.get(arg1, set()):
                return False
            if arg1.startswith("?") or arg2.startswith("?"):
                continue
            if arg1 != arg2:
                return False
        return True


class Condition(AtomicActionPart):
    def __init__(self, condition: Literal):
        self.__condition = condition

    def __hash__(self) -> int:
        return hash(self.__condition)

    def __eq__(self, other: 'Condition') -> bool:
        return (    isinstance(other, Condition)
                and self.__condition == other.__condition)

    @property
    def condition(self):
        return self.__condition

    def find_args(self) -> Set[str]:
        if isinstance(self.__condition, Literal):
            return self._find_args_in_literal(self.__condition)
        raise NotImplementedError("Other Conditions are not supported!")

    def is_threatened_by(self,
                         transition: 'Transition',
                         distinct_args: Dict[str, Set[str]]) -> bool:
        for effect in transition.effects:
            if self._are_possibly_the_same(self.__condition,
                                           effect,
                                           distinct_args):
                return True
        return False

    def to_string(self, indent) -> str:
        return indent + literal_to_string(self.__condition) + "\n"


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
            # `del_effect` is not related to this transition
            return set()

        statements = set().union(*self.__conditions,
                                 {self.__main_effect.negate()},
                                 {del_effect.negate()})
        # TODO: We are supposed to check if `condition` is a logical
        #       consequence of `statement` or not. In the following,
        #       for simplicity, I have not used some other knowledge in
        #       action's precondition, the problem itself, or even the
        #       possible unification, so it might be not precise. I
        #       should fix this!
        if statements.issuperset(set(conditions)):
            self.__effects.append(del_effect)
            return common_variables_ids

        return set()

    def find_args(self) -> Set[str]:
        args = set().union(*[self._find_args_in_literal(condition)
                             for condition in self.__conditions])
        args = args.union(*[self._find_args_in_literal(effect)
                            for effect in self.__effects])
        return args

    @property
    def effects(self):
        return self.__effects.copy()

    @property
    def conditions(self):
        return self.__conditions.copy()

    @property
    def has_condition(self):
        return len(self.__conditions) != 0

    def is_threatened_by(self,
                         transition: 'Transition',
                         distinct_args: Dict[str, Set[str]]) -> bool:
        if self == transition:
            return False
        for effect in transition.effects:
            for condition in self.__conditions:
                if self._are_possibly_the_same(effect,
                                               condition,
                                               distinct_args):
                    return True

        # Delete effect should not be after the add effect.
        # It somehow might be confusing because the interpretation
        # is like our negative effect is threatened by another
        # positive effect, so the positive effect should be placed
        # after the negative one.
        if not self.__main_effect.negated:
            return False
        if (    not transition.__main_effect.negated
            and self._are_possibly_the_same(self.__effects[0],
                                            transition.__effects[0],
                                            distinct_args)):
            return True

        return False

    def to_string(self, indent) -> str:
        output = ""
        if not self.__conditions:
            for effect in self.__effects:
                output += f"{indent}{literal_to_string(effect)}\n"
            return output

        def literals_to_string(indent, literals):
            if not literals:
                return indent + "(and)\n"
            if len(literals) == 1:
                return indent + literal_to_string(literals[0]) + "\n"
            output  = indent + "(and "
            output += f"\n{indent}     ".join([literal_to_string(literal)
                                               for literal in literals])
            output += f"\n{indent})\n"
            return output

        output  = indent + "(when\n"
        output += literals_to_string(indent + "      ", self.__conditions)
        output += literals_to_string(indent + "      ", self.__effects)
        output += indent + ")\n"
        return output


class MicroAction:
    def __init__(self):
        self.__preconditions: List[Condition] = []
        self.__transitions: List[Transition] = []
        self.__args = set()

    @property
    def args(self):
        return self.__args

    @property
    def preconditions(self):
        return self.__preconditions  # Guaranteed to be an ordered list

    @property
    def has_precondition(self):
        return len(self.__preconditions) > 0

    @property
    def transitions(self):
        return self.__transitions  # Guaranteed to be an ordered list

    @property
    def has_transition(self):
        return len(self.__transitions) > 0

    @property
    def effects(self):
        return [e for t in self.__transitions for e in t.effects]

    def __copy__(self):
        shallow_copy = MicroAction()
        shallow_copy.__preconditions = self.__preconditions.copy()
        shallow_copy.__transitions = self.__transitions.copy()
        shallow_copy.__args = self.__args.copy()
        return shallow_copy

    def __deepcopy__(self, memo):
        # To improve the performance (especially for beam search), we
        # assume two preconditions (or two transitions) are different
        # only if their object IDs (addresses) are different.
        # Thus, we disable deep copy of MicroAction to prevent cloning 
        # the same preconditions or transitions in with different IDs.
        raise Exception("Deep copy for `MicroAction` is disabled to prevent "
                        "unexpected bugs!")

    def copy(self):
        return copy.copy(self)

    def add_precondition(self, condition: Condition):
        if condition in self.__preconditions:
            return self
        self.__preconditions.append(condition)
        self.__preconditions.sort(key=id)
        self.__args.update(condition.find_args())
        return self

    def add_transition(self, transition: Transition):
        if transition in self.__transitions:
            return self
        self.__transitions.append(transition)
        self.__transitions.sort(key=id)
        self.__args.update(transition.find_args())
        return self

    def is_threatened_by(self,
                         other: 'MicroAction',
                         distinct_args: Dict[str, Set[str]]) -> bool:
        if self == other:
            return False
        parts = self.__preconditions + self.__transitions
        return any(part.is_threatened_by(other_transition,
                                         distinct_args)
                   for other_transition in other.__transitions 
                   for part in parts)

    def merge(self, other: 'MicroAction') -> 'MicroAction':
        conditions = set().union(self.__preconditions, other.__preconditions)
        self.__preconditions = sorted(conditions, key=id)
        transitions = set().union(self.__transitions, other.__transitions)
        self.__transitions = sorted(transitions, key=id)
        self.__args.update(other.__args)
        return self

    def update_partial_state(self,
                             partial_state: Set[Condition],
                             distinct_args: Dict[str, Set[str]]
                            ) -> Set[Condition]:
        partial_state.update(self.__preconditions)
        new_partial_state = set()
        for condition in partial_state:
            for transition in self.__transitions:
                if condition.is_threatened_by(transition,
                                              distinct_args):
                    break
            else:
                new_partial_state.add(condition)
        for transition in self.__transitions:
            if transition.has_condition:
                continue
            new_partial_state.update(Condition(e) for e in transition.effects)
        return new_partial_state

    def to_string(self, action_name, args, indent) -> str:
        args = ' '.join([f"{a.name} - {a.type_name}"
                         for a in args
                         if a.name in self.__args])
        conditions = []
        for precondition in self.__preconditions:
            conditions.append(precondition.to_string(indent + "\t\t\t"))
        conditions.sort()
        conditions = "".join(conditions)
        preconditions = f"{indent}\t\t(and\n{conditions}{indent}\t\t)\n"
        effects = []
        for transition in self.__transitions:
            effects.append(transition.to_string(indent + "\t\t\t"))
        effects.sort()
        effects = f"{indent}\t\t(and\n{''.join(effects)}{indent}\t\t)\n"

        output  = f"{indent}(:action {action_name}\n"
        output += f"{indent} :parameters ({args})\n"
        output += f"{indent} :precondition\n{preconditions}"
        output += f"{indent} :effect\n{effects}"
        output += f"{indent})"
        return output
