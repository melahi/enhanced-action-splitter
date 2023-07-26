#! /usr/bin/env python3


import sys

# TODO: The following lines is an ugly way to override argument handling
#       implemented in the `options.py` file.
arguments = sys.argv[1:]
sys.argv = ["dummy1", "dummy2", "dummy3"]

import random
random.seed(14)

import timers
import pddl_parser

from .knowledge import Knowledge
from .action import Action
from .task_to_string import output
from .plan_merger import main as plan_merger


SIZE_THRESHOLD = 1000000
RANDOM_WALKS_TIMEOUT = 500


def split():
    task = pddl_parser.open(arguments[0], arguments[1])
    with timers.timing("Extract knowledge", block=True):
        knowledge = Knowledge(task)
    with timers.timing("Splitting actions", block=True):
        # print("size threshold:", SIZE_THRESHOLD / len(task.actions))
        print("random walks timeout:",
              max(10.0, RANDOM_WALKS_TIMEOUT / len(task.actions)))
        actions = [Action(knowledge,
                          action,
                          SIZE_THRESHOLD / len(task.actions),
                          max(10, RANDOM_WALKS_TIMEOUT / len(task.actions)))
                   for action in task.actions]
    output(task, actions)


def merge_plan():
    task = pddl_parser.open(arguments[0], arguments[1])
    splitted = pddl_parser.open(arguments[2], arguments[3])
    plan_merger(task, splitted, arguments[4])


def main():
    print("SIZE THRESHOLD:", SIZE_THRESHOLD)
    print("RANDOM WALKS TIMEOUT:", RANDOM_WALKS_TIMEOUT)

    if len(arguments) == 2:
        split()
    elif len(arguments) == 5:
        merge_plan()
    else:
        raise ValueError("Unknown number of arguments!")


if __name__ == "__main__":
    main()
