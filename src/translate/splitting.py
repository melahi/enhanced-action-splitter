#! /usr/bin/env python3


from typing import List, Tuple, Iterable
from itertools import chain
from functools import reduce

import normalize
import pddl_parser
from invariant_finder import find_invariants
from pddl.tasks import Task
from pddl.actions import Action
from pddl.conditions import Condition, Conjunction, Atom


Predicate = Tuple[str, Iterable[str]]  # predicate type


class Knowledge:
    """Extracts and provide predicates' knowledge
    
    For some predicates, we can partition their arguments to the
    "counted variable" and the other "parameters". By, this
    partitioning, we can uniquely determine the value of the
    "counted variable" argument, when we are given the values for the
    other "parameters", in each possible state.

    This class extracts and provides this kind of knowledge.
    """

    def __init__(self, task: Task) -> None:
        self.__predicates = dict()  # A dictionary from predicates to the list
                                    # their <omitted_pos>s (or, the position of
                                    # their <counted variable>s).
        self.__extract_knowledge(task)

    def get_relations(self, predicate: Predicate) -> List[Tuple[str, str]]:
        relations = []
        print("<Predicate>:", predicate)
        for counted_variable_position in self.__predicates.get(predicate[0], []):
            counted_variable = predicate[1][counted_variable_position]
            for arg in predicate[1]:
                if arg == counted_variable:
                    continue
                relations.append((arg, counted_variable))
        return relations

    def __extract_knowledge(self, task):
        normalize.normalize(task)
        for invariant in find_invariants(task, None):
            for part in invariant.parts:
                if part.omitted_pos != -1:
                    (self
                     .__predicates
                     .setdefault(part.predicate, [])
                     .append(part.omitted_pos))


class Graph:
    """Directed graph representing the influential relation

    Maintains the influential relation among variables. In other words, the
    graph has an edge (u, v) if and only if the variable u has an influence on
    variable v (or, variable v depends on variable u).

    Additionally, this class produces a topological order of the vertices.
    """
    Vertex = str  # Vertex type

    def __init__(self) -> None:
        self.__graph = {}
    
    def add_vertex (self, vertex: Vertex) -> 'Graph':
        self.__graph.setdefault(vertex, [])
        return self

    def add_edge(self, source: Vertex, destination: Vertex) -> 'Graph':
        self.__graph.setdefault(source, []).append(destination)
        return self

    def topological_order(self) -> List[Vertex]:
        # TODO: Complete this function
        return [*self.__graph]


class ActionSplitter:
    """Decomposes each action into a series of micro-actions"""

    def __init__(self, knowledge: Knowledge) -> None:
        self.__knowledge = knowledge

    def split_action(self, action: Action) -> List[Action]:
        return []


if __name__ == "__main__":
    print("Parsing...")
    task = pddl_parser.open()
    print("Printing before normalizing:")
    task.dump()
    print("Normalizing...")
    normalize.normalize(task)
    print("Dumping task:")
    task.dump()
    print("Finding invariants...")
    print("NOTE: not passing in reachable_action_params.")
    print("This means fewer invariants might be found.")