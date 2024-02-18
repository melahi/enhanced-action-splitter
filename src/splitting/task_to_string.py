from typing import List
from itertools import chain
from functools import reduce

import pddl
from pddl import Task, Atom, Conjunction, Literal

from .action import Action
from .common import literal_to_string, get_conditions


def output(task: Task, actions: List[Action], domain_file, problem_file):
    task = __update_task(task, actions)
    domain_str = __domain_to_string(task)
    problem_str = __problem_to_string(task)
    __write(domain_str, problem_str, domain_file, problem_file)


def __update_task(task: Task, actions: List[Action]) -> Task:
    STEP_TYPE = pddl.Type(Action.STEP_TYPE)
    def define_predicate(task: Task, predicate_info):
        predicate_name, args_types, initial_value = predicate_info
        task.predicates.append(pddl.Predicate(predicate_name, args_types))
        init = Atom(predicate_name, initial_value)
        task.init.append(init)
        # task.goal = Conjunction((task.goal, init)).simplified()
        if predicate_name == "start_procedure":
            task.goal = Conjunction((task.goal, init)).simplified()
        return task

    task.types.append(STEP_TYPE)
    task = define_predicate(task, (Action.START_PROCEDURE, (), ()))
    new_predicates = chain.from_iterable(action.new_predicates
                                         for action in actions)
    task = reduce(define_predicate, new_predicates, task)
    task.predicates = [p for p in task.predicates if p.name != "="]
    task.init = [l for l in task.init
                 if isinstance(l, Literal) and l.predicate != "="]
    task.init = sorted(task.init)
    new_objects = set().union(*[action.new_objects for action in actions])
    new_objects = sorted(new_objects, key=lambda x: int(x.split("_")[-1]))
    task.objects.extend([pddl.TypedObject(new_object, STEP_TYPE)
                         for new_object in new_objects])
    task.actions = actions
    return task


DOMAIN_TEMPLATE = """(define (domain {domain_name})
(:requirements {requirements})
(:types {types})
(:constants {constants})
(:predicates {predicates})
{actions}
)
"""

def __domain_to_string(task: Task) -> str:
    types  = [f"{t.name} - {t.basetype_name}"
              for t in task.types if t.basetype_name]
    types += [t.name for t in task.types if not t.basetype_name]
    types  = " ".join(types)
    objects = {}
    for obj in task.objects:
        objects.setdefault(obj.type_name, []).append(obj.name)
    constants  = [f"{' '.join(objects[t])} - {t}" for t in objects if t]
    constants += [f"{' '.join(objects[t])}" for t in objects if not t]
    constants = "\n            ".join(constants)
    requirements = " ".join(r
                            for r in task.requirements.requirements
                            if r.lower() != ":action-costs")
    def predicate_str(predicate):
        arguments = [f"{a.name} - {a.type_name}" if a.type_name else a.name
                     for a in predicate.arguments]
        return f"({' '.join([predicate.name, *arguments])})"
    predicates = "\n             ".join(predicate_str(p)
                                        for p in task.predicates)
    actions = "\n\n".join(action.to_string("") for action in task.actions)
    return DOMAIN_TEMPLATE.format(domain_name=task.domain_name,
                                  requirements=requirements,
                                  types=types,
                                  constants=constants,
                                  predicates=predicates,
                                  actions=actions)



PROBLEM_TEMPLATE = """(define (problem {problem_name})
(:domain {domain_name})
(:init {init})
(:goal {goal})
)
"""

def __problem_to_string(task: Task):
    init = "\n       ".join(literal_to_string(l) for l in task.init)
    goals  = "(and "
    goals += "\n           ".join(literal_to_string(l)
                                  for l in get_conditions(task.goal))
    goals += ")"
    return PROBLEM_TEMPLATE.format(problem_name=task.task_name,
                                   domain_name=task.domain_name,
                                   init=init,
                                   goal=goals)


def __write(domain: str, problem: str, domain_file: str, problem_file: str):
    with open(domain_file, "w") as output_file:
        output_file.write(domain)
    with open(problem_file, "w") as output_file:
        output_file.write(problem)
