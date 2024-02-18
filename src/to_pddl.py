from typing import List

import pddl.conditions
from splitting import MicroAction

class Literal:
    def __init__(self, literal: pddl.conditions.Literal):
        self.__literal = literal

    def __str__(self):
        print(self.__literal)
        return f"({' '.join([self.__literal.predicate, *self.__literal.args])})"


class Action:
    def __init__(self, name, args, preconditions, effects):
        self.__name = name
        self.__args = args
        self.__preconditions = [Literal(p) for p in preconditions]
        self.__effects = [Literal(e) for e in effects]

    def __str__(self):
        preconditions = [str(p) for p in self.__preconditions]
        preconditions = ("\n" + " " * 27).join(preconditions)
        effects = [str(e) for e in self.__effects]
        effects = ("\n" + " " * 22).join(effects)
        output  = f"    (:action {self.__name}\n"
        output += f"        :parameters ({' '.join(self.__args)})\n"
        output += f"        :precondition (and {preconditions})\n"
        output += f"        :effects (and {effects}))\n"
        return output


def to_pddl(actions: List[List[MicroAction]]):
    for action in actions:
        for index, micro_action in enumerate(action):
            pddl_action = Action(name=micro_action.name(index),
                                 args=micro_action.args,
                                 preconditions=micro_action.preconditions,
                                 effects=micro_action.effects)
            print(pddl_action)

