#! /usr/bin/env pypy3


import sys

import random
random.seed(14)


# TODO: The following lines is an ugly way to override argument handling
#       implemented in the `options.py` file.
sys.argv = ["dummy1", "dummy2", "dummy3"]
import timers
import pddl_parser

from .knowledge import Knowledge
from .action import Action
from .task_to_string import output
from .plan_merger import main as plan_merger


def split(max_grounded_actions, max_search_time, domain, problem, split_domain, split_problem):
    print("Domain:", domain)
    print("Problem:", problem)
    task = pddl_parser.open(domain, problem)
    with timers.timing("Extract knowledge", block=True):
        knowledge = Knowledge(task)
    with timers.timing("Splitting actions", block=True):
        actions = [Action(knowledge,
                          action,
                          max_grounded_actions / len(task.actions),
                          max(50, max_search_time / len(task.actions)))
                   for action in task.actions]
    output(task, actions, split_domain, split_problem)


def merge_plan(domain, problem, split_domain, split_problem, input_plan, output_plan):
    task = pddl_parser.open(domain, problem)
    splitted = pddl_parser.open(split_domain, split_problem)
    plan_merger(task, splitted, input_plan, output_plan)


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
