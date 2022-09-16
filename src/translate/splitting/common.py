from typing import Tuple, Iterable
from itertools import chain

from pddl import Literal, Conjunction, Truth, TypedObject


Predicate = Tuple[str, Iterable[str]]  # predicate type


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
    raise ValueError("Unexpected condition type!")


