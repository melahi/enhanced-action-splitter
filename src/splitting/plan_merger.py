#! /usr/bin/env python3
from typing import List, Dict

from pddl.pddl_types import TypedObject
from pddl.tasks import Task


class GroundAction:
    def __init__(self, action: 'Action') -> None:
        self.__action = action
        self.__args = [None] * len(action.defaults)
        self.__current_step = 0

    def __str__(self):
        if self.__current_step != len(self.__action.procedure):
            raise Exception(f"Not completed procedure for {self.__action.name}"
                            f"({self.__current_step}"
                            f"/{len(self.__action.procedure)})")
        args = [a if a is not None else d
                for a, d in zip(self.__args, self.__action.defaults)]
        return f"({' '.join([self.__action.name] + args)})"

    def add_step(self, args):
        for arg, value in zip(self.__action.procedure[self.__current_step],
                              args):
            arg_index = self.__action.indices[arg]
            if self.__args[arg_index] is None:
                self.__args[arg_index] = value
            elif self.__args[arg_index] != value:
                raise ValueError(f"Action {self.__action.name}): "
                                 f"Expected {self.__args[arg_index]}, "
                                 f"got {value}!")
        self.__current_step += 1
        return self


class Action:
    def __init__(self, name: str, args: List[TypedObject], default_objects):
        self.name = name
        self.indices = {a.name: i for i, a in enumerate(args)}
        self.defaults = [default_objects.get(a.type_name, None) for a in args]
        self.procedure: List[List[str]] = []

    def add_step(self, index, args):
        self.procedure.extend([None] * max(0, (index - len(self.procedure) + 1)))
        self.procedure[index] = [a.name for a in args]

    def instance(self) -> GroundAction:
        return GroundAction(self)


def split_name(name: str):
    last_index = name.rfind('_')
    if last_index == -1 or not name[last_index + 1:].isdigit():
        return (name, 0)
    return name[:last_index], int(name[last_index + 1:])


def find_default_objects(task: Task):
    parents = {t.name: t.basetype_name for t in task.types}
    default_objects = {}
    for object in task.objects:
        current_type = object.type_name
        while current_type is not None:
            default_objects.setdefault(current_type, object.name)
            current_type = parents.get(current_type, None)
    return default_objects


def create_actions(task: Task, splitted: Task):
    default_objects = find_default_objects(task)
    actions = {a.name: Action(a.name, a.parameters, default_objects)
               for a in task.actions}
    for micro_action in splitted.actions:
        name, index = split_name(micro_action.name)
        actions[name].add_step(index, micro_action.parameters)
    return actions


def read_plan(plan_file: str) -> List[str]:
    plan = []
    with open(plan_file, mode="r") as input:
        for line in input:
            if line[0] == ";":
                continue
            plan.append(line.strip()[1:-1].lower())  # Drop parentheses
    return plan


def merge_plan(actions: Dict[str, Action], plan: List[str]) -> List[GroundAction]:
    merged_plan = []
    for step in plan:
        elements = step.split()
        action, index = split_name(elements[0])
        if index == 0:
            merged_plan.append(actions[action].instance())
        merged_plan[-1].add_step(elements[1:])
    return merged_plan


def output(merged_plan: List[GroundAction], output_file: str):
    with open(output_file, mode="w") as output:
        output.write("\n".join(str(s) for s in merged_plan))


def main(task: Task, splitted: Task, plan_file: str, output_file: str):
    actions = create_actions(task, splitted)
    plan = read_plan(plan_file)
    merged_plan = merge_plan(actions, plan)
    output(merged_plan, output_file)


if __name__ == "__main__":
    main()
