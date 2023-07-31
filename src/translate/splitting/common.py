from typing import Tuple, List, Union
from itertools import chain

from pddl import Literal, Conjunction, Truth, TypedObject


Predicate = Tuple[str, List[str]]  # predicate type


def is_variable(argument: Union[str, TypedObject]):
    return ((argument.name if isinstance(argument, TypedObject) else argument)
            .startswith("?"))


def literal_to_string(literal: Literal) -> str:
    elements = [literal.predicate]
    elements += [a.name if isinstance(a, TypedObject) else a
                 for a in literal.args]
    predicate = f"({' '.join(elements)})"
    if literal.negated:
        return f"(not {predicate})"
    return predicate


def get_conditions(condition):
    if isinstance(condition, Conjunction):
        return list(chain(*[get_conditions(part)
                            for part in condition.parts]))
    if isinstance(condition, Literal):
        return [condition]
    if isinstance(condition, Truth):
        return []
    raise ValueError(f"Unexpected condition type: {type(condition)}")