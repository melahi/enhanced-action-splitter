#! /usr/bin/env python3


from pddl.tasks import Task

from .knowledge import Knowledge
from .action import Action
from .task_to_string import output


MAX_ARGUMENTS = 4


def find_default_objects(task: Task):
    parents = {t.name: t.basetype_name for t in task.types}
    defaults = {}
    for obj in task.objects:
        type_name = obj.type_name
        while type_name:
            defaults.setdefault(type_name, obj.name)
            type_name = parents.get(type_name, None)
    return defaults


def filter_not_instantiable_actions(defaults, task: Task) -> Task:
    actions = []
    for action in task.actions:
        for parameter in action.parameters:
            if parameter.type_name not in defaults:
                break
        else:
            actions.append(action)
    task.actions = actions
    return task


def main(task: Task):
    print("Extract knowledge...")
    default_objects = find_default_objects(task)
    task = filter_not_instantiable_actions(default_objects, task)
    knowledge = Knowledge(task)
    print("Splitting actions ...")
    actions = [Action(knowledge, action, MAX_ARGUMENTS, default_objects)
               for action in task.actions]
    output(task, actions)


if __name__ == "__main__":
    import pddl_parser
    print("Parsing...")
    task = pddl_parser.open()
    main()