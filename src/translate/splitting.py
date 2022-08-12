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
    """Directed graph (representing the influential relation)

    Maintains the influential relation among variables. In other words,
    the graph has an edge (u, v) if and only if the variable u has an
    influence on
    variable v (or, variable v depends on variable u).

    Additionally, this class produces a topological order of the
    vertices.
    """
    Vertex = str  # Vertex type

    def __init__(self, vertices: List[Vertex] = []) -> None:
        self.__graph = {vertex: [] for vertex in vertices}

    def __str__(self) -> str:
        return str(self.__graph)
    
    def add_edge(self, edge: Tuple[Vertex, Vertex]) -> 'Graph':
        source, destination = edge
        self.__graph.setdefault(source, []).append(destination)
        return self

    def topological_order(self) -> List[Vertex]:
        def dfs(vertex, visited, order):
            visited.append(vertex)
            for destination in self.__graph[vertex]:
                if destination in visited:
                    continue
                visited, order = dfs(destination, visited, order)
            return visited, [vertex] + order
        
        order = []
        visited = []
        for vertex in self.__graph:
            if vertex not in order:
                visited, order = dfs(vertex, visited, order)

        return order


class ActionSplitter:
    """Decomposes each action into a series of micro-actions"""

    def __init__(self, knowledge: Knowledge) -> None:
        self.__knowledge = knowledge

    def split_action(self, action: Action) -> List[Action]:
        conditions = self.__get_conditions(action.precondition)
        parameters = map(lambda parameter: parameter.name, action.parameters)
        influential_order = self.__order_variables(parameters, conditions)

    @staticmethod
    def __get_conditions(precondition: Condition) -> List[Condition]:
        if isinstance(precondition, Conjunction):
            return precondition.parts
        return [precondition]
        
    def __order_variables(self, variables: List[str], conditions) -> List[str]:
        """Orders the vertices based on their influential relations"""

        # Filter out any condition except positive literals
        conditions = filter(lambda condition: isinstance(condition, Atom),
                            conditions)
        predicates = map (lambda atom: (atom.predicate, atom.args), conditions)

        # Constructing the influential graph
        graph = Graph(variables)
        relations = list(chain(*[self.__knowledge.get_relations(predicate)
                                 for predicate in predicates]))
        graph = reduce(Graph.add_edge, relations, graph)

        return graph.topological_order()


if __name__ == "__main__":
    print("Parsing...")
    task = pddl_parser.open()
    print("Extract knowledge...")
    knowledge = Knowledge(task)
    splitter = ActionSplitter(knowledge)
    print("Splitting actions ...")
    for action in task.actions:
        splitter.split_action(action)