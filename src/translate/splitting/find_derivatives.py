#! /usr/bin/env python3

import random
random.seed(14)

import timers
import pddl_parser
from pddl import Literal, Atom, TypedObject

from .knowledge import Knowledge
from .common import get_conditions, Predicate, literal_to_string



def to_my_predicate(predicate: Literal) -> Predicate:
    return (predicate.predicate, [a.name if isinstance(a, TypedObject) else a
                                  for a in predicate.args])


def find_derivatives(domain: str, problem: str):
    task = pddl_parser.open(domain, problem)
    not_found_anything = True
    with timers.timing("Extract knowledge", block=True):
        knowledge = Knowledge(task)
    for action in task.actions:
        not_founded = True
        for condition in get_conditions(action.precondition):
            if not isinstance(condition, Atom):
                continue
            my_predicate = to_my_predicate(condition)
            for omittable in knowledge.omittable_arguments(my_predicate):
                if not_founded:
                    not_founded = False
                    not_found_anything = False
                    print("Action:", action.name)
                condition_str = literal_to_string(condition)
                print("    {:<25}\tomittable => {}".format(omittable,
                                                           condition_str))

    if not_found_anything:
        print("Not found anything for this domain!")


if __name__ == "__main__":
    from .main import arguments
    find_derivatives(arguments[0], arguments[1])