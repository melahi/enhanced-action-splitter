#! /usr/bin/env python3


import timers
from pddl.tasks import Task

from .knowledge import Knowledge
from .action import Action
from .task_to_string import output


SIZE_THRESHOLD = 10000


def main(task: Task):
    with timers.timing("Extract knowledge", block=True):
        knowledge = Knowledge(task)
    with timers.timing("Splitting actions", block=False):
        actions = [Action(knowledge, action, SIZE_THRESHOLD)
                   for action in task.actions]
    output(task, actions)


if __name__ == "__main__":
    import pddl_parser
    print("Parsing...")
    task = pddl_parser.open()
    main()