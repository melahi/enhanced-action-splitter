#! /usr/bin/env python3


from typing import List
from dataclasses import dataclass

from invariant_finder import find_invariants
from normalize import normalize
from pddl.conditions import Atom
from pddl.tasks import Task


@dataclass
class Array:
    name: str
    value_position: int


class ArrayFinder:
    def __init__(self, task: Task):
        self.__arrays: List[Array] = []
        self.__find_dynamic_arrays(task)
        self.__find_static_arrays(task)

    def dump(self):
        print("All possible arrays:")
        for array in self.__arrays:
            print(array)

    def __find_dynamic_arrays(self, task: Task):
        normalize(task)
        # TODO: We can set <action_reachable_params> to generate
        #       potentially more invariants, in the following.
        #       Additionally, I've ignored the initial state, and assumed
        #       no invariant has weight of more than one, which might be
        #       not true; but, it shouldn't have adverse effects on our
        #       approach.
        for invariant in find_invariants(task, None):
            for part in invariant.parts:
                if part.omitted_pos != -1:
                    (self
                     .__arrays
                     .append(Array(part.predicate, part.omitted_pos)))

    def __find_static_arrays(self, task: Task):
        initial_state = [(fact.predicate, fact.args)
                         for fact in task.init
                         if isinstance(fact, Atom)]
        def process_candidate(candidate):
            return self.__process_static_candidates(initial_state, candidate)

        for candidate in self.__find_static_candidates(task):
            for value_position in process_candidate(candidate):
                self.__arrays.append(Array(candidate, value_position))

    @staticmethod
    def __find_static_candidates(task: Task):
        candidates = {predicate.name for predicate in task.predicates
                                     if predicate.get_arity() > 1}
        for action in task.actions:
            for effect in action.effects:
                candidates.discard(effect.literal.predicate)
        return candidates

    @staticmethod
    def __process_static_candidates(initial_state, candidate):
        """Determines all possible value positions

        In partitioning the arguments into the value and indices, this
        function determines all possible value positions in all valid
        partitioning. 
        """

        records = [args for predicate, args in initial_state
                        if predicate == candidate]
        if len(records) == 0:
            return []
        arity = len(records[0])
        value_positions = []
        for value_position in range(arity):
            indices = {record[:value_position] + record[value_position + 1:]
                       for record in records}
            if len(indices) < len(records):
                # At least for one index there exists two values
                continue
            value_positions.append(value_position)
        return value_positions


if __name__ == "__main__":
    import pddl_parser

    print("Parsing...")
    task = pddl_parser.open()
    print("Extract knowledge...")
    arrays = ArrayFinder(task)
    arrays.dump()
