#! /usr/bin/env python3


from pddl.tasks import Task

from .knowledge import Knowledge
from .action import Action
from .task_to_string import output


SIZE_THRESHOLD = 100000


def main(task: Task):
    print("Extract knowledge...")
    knowledge = Knowledge(task)
    print("Splitting actions ...")
    actions = [Action(knowledge, action, SIZE_THRESHOLD)
               for action in task.actions]
    output(task, actions)


if __name__ == "__main__":
    import pddl_parser
    print("Parsing...")
    task = pddl_parser.open()
    main()