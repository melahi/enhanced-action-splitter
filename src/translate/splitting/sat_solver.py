from typing import Iterable
from z3 import Bool, Not, Or, Solver, sat

from pddl import Literal, Atom, TypedObject


class Context:
    def __init__(self):
        self.__solver = Solver()

    def add_scope(self):
        self.__solver.push()
        return self

    def drop_scope(self):
        self.__solver.pop()
        return self

    def add_clause(self, clause: Iterable[Literal]):
        def get_boolean(literal: Literal):
            arguments = (a.name if isinstance(a, TypedObject) else a
                         for a in literal.args)
            id = f"{literal.predicate}({', '.join(arguments)})"
            return Bool(id) if isinstance(literal, Atom) else Not(Bool(id))
        self.__solver.add(Or(*(get_boolean(l) for l in clause)))
        return self

    def is_satisfiable(self) -> bool:
        return self.__solver.check() == sat