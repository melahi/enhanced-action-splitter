#! /usr/bin/env python3


from pddl.tasks import Task

from .knowledge import Knowledge
from .action import Action
from .task_to_string import output


MAX_ARGUMENTS = 4


def main(task: Task):
    print("Extract knowledge...")
    knowledge = Knowledge(task)
    print("Splitting actions ...")
    actions = [Action(knowledge, action, MAX_ARGUMENTS)
               for action in task.actions]
    output(task, actions)


if __name__ == "__main__":
    import pddl_parser
    print("Parsing...")
    task = pddl_parser.open()
    main()