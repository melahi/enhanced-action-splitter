#! /usr/bin/env pypy3

import pddl
import pddl_parser

from splitting.action import Action
from splitting.micro_action import Condition, Transition, MicroAction
from splitting.common import get_conditions
from splitting.task_to_string import output


class NoCostAction(Action):
    def __init__(self, action: pddl.Action):
        main_micro_action = MicroAction()
        for condition in get_conditions(action.precondition):
            main_micro_action.add_precondition(Condition(condition))
        for transition in self.__get_transitions(action.effects):
            main_micro_action.add_transition(transition)
        self._set_micro_actions([main_micro_action])
        self._set_name(action.name)
        self._set_args(action.parameters)

    @property
    def new_objects(self):
        return []

    @property
    def new_predicates(self):
        return []

    def __get_transitions(self, raw_effects):
        effects = []
        for effect in raw_effects:
            if isinstance(effect, pddl.SimpleEffect):
                effects.append(([], effect.effect))
            elif isinstance(effect, pddl.ConditionalEffect):
                conditions = get_conditions(effect.condition)
                effects.append((conditions, effect.effect))
            elif isinstance(effect, pddl.Effect):
                conditions = get_conditions(effect.condition)
                effects.append((conditions, effect.literal))
            else:
                raise NotImplementedError("Unknown effect!")
        transitions = []
        for conditions, effect in effects:
            transitions.append(Transition(conditions, effect, set()))
        return transitions


def main():
    # task = pddl_parser.open(arguments[0], arguments[1])
    task = pddl_parser.open()
    actions = [NoCostAction(action) for action in task.actions]
    output(task, actions)


if __name__ == "__main__":
    main()

