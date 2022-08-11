#! /usr/bin/env python3


from typing import List

import normalize
import pddl_parser
from pddl.actions import Action


class Knowledge:
    """Extracts and provide predicates' knowledge"""

    def __init__(self) -> None:
        pass


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