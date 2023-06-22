import copy
from typing import List, Tuple, Set, Dict, Generic, TypeVar


Vertex = TypeVar('Vertex')
class Graph(Generic[Vertex]):
    """Directed graph (representing the influential relation)

    Maintains the influential relation among variables. In other words,
    the graph has an edge (u, v) if and only if the variable u has an
    influence on
    variable v (or, variable v depends on variable u).

    Additionally, this class produces a topological order of the
    vertices.
    """
    def __init__(self, vertices: List[Vertex] = []):
        self.__graph = {vertex: set() for vertex in vertices}

    def __str__(self) -> str:
        return str(self.__graph)

    def __contains__(self, vertex: Vertex):
        return vertex in self.__graph

    @property
    def vertices(self):
        return [*self.__graph]

    def add_edge(self, edge: Tuple[Vertex, Vertex]):
        source, destination = edge
        self.__graph.setdefault(source, set()).add(destination)
        return self

    def neighbors(self, vertex: Vertex):
        return self.__graph[vertex].copy()

    def remove_vertex(self, vertex: Vertex):
        if vertex not in self.__graph:
            return self
        self.__graph.pop(vertex)
        for _, neighbors in self.__graph.items():
            neighbors.discard(vertex)
        return self

    def make_acyclic(self, vertex_priority=None):
        order = {v: i
                 for i, v in enumerate(self.topological_order(vertex_priority))}
        for vertex in self.__graph.keys():
            self.__graph[vertex] = {neighbor
                                    for neighbor in self.__graph[vertex]
                                    if order[neighbor] < order[vertex]}
        return self

    def topological_order(self, vertex_priority=None) -> List[Vertex]:
        # NOTE: The graph is assumed to be a "DEPENDENCY" graph!

        # `vertex_priority`: is a function from `Vertex` to a totally ordered
        #                    value. It will be used as the `key` input for
        #                    `list.sort()`.
        if vertex_priority is None:
            return self.__topological_order()
        # return self.__topological_order_old(vertex_priority)
        return self.__topological_order_precise(vertex_priority)

    def __topological_order(self) -> List[Vertex]:
        def dfs(vertex, visited, order):
            stack = [(False, vertex)]
            while stack:
                completed, vertex = stack.pop()
                if completed:
                    # NOTE: The graph is assumed to be a "DEPENDENCY" graph,
                    #       otherwise, we should use the following line instead.
                    # order = [vertex] + order
                    order.append(vertex)
                    continue
                if vertex in visited:
                    continue
                visited.append(vertex)
                neighbors = list(self.__graph[vertex])
                stack.append((True, vertex))
                stack.extend([(False, n) for n in neighbors])
            return visited, order
        
        visited = []
        order = []
        for vertex in self.__graph:
            if vertex not in order:
                visited, order = dfs(vertex, visited, order)
        return order

    def __topological_order_precise(self, vertex_priority):
        # This is a more accurate version of topological order. The old
        # version, `__topological_order_old`, might be faster.
        ordered = []
        vertices = sorted(self.__graph, key=vertex_priority, reverse=True)
        while vertices:
            for i, vertex in enumerate(vertices):
                for dependency in self.__graph[vertex]:
                    if dependency not in ordered:
                        break
                else:
                    ordered.append(vertices.pop(i))
                    break
        return ordered

    def __topological_order_old(self, vertex_priority):
        def dfs(vertex, visited, order):
            stack = [(False, vertex)]
            while stack:
                completed, vertex = stack.pop()
                if completed:
                    # NOTE: The graph is assumed to be a "DEPENDENCY" graph,
                    #       otherwise, we should use the following line instead.
                    # order = [vertex] + order
                    order.append(vertex)
                    continue
                if vertex in visited:
                    continue
                visited.append(vertex)
                neighbors = list(self.__graph[vertex])
                if vertex_priority:
                    neighbors.sort(key=vertex_priority, reverse=True)
                stack.append((True, vertex))
                stack.extend([(False, n) for n in neighbors])
            return visited, order

        def get_components():
            parent = {v: v for v in self.__graph}
            priority = {v: vertex_priority(v) if vertex_priority else 0
                        for v in self.__graph}
            def find_parent(vertex):
                if parent[vertex] != parent[parent[vertex]]:
                    parent[vertex] = find_parent(parent[vertex])
                return parent[vertex]
            def join(source, destination):
                parent_source = find_parent(source)
                parent_destination = find_parent(destination)
                parent[parent_destination] = parent_source
                priority[parent_source] = max(priority[parent_source],
                                              priority[parent_destination])

            for source, destinations in self.__graph.items():
                for destination in destinations:
                    join(source, destination)

            components = {}
            for vertex in self.__graph:
                components.setdefault(find_parent(vertex), []).append(vertex)
            components = [v for _, v in components.items()]
            components.sort(key=lambda v: priority[find_parent(v[0])])
            return components

        order = []
        visited = []
        for component in get_components():
            assert set(component).isdisjoint(order), ("New component is "
                                                      "overlapped with "
                                                      "currently visited "
                                                      "nodes!")
            if vertex_priority is not None:
                component.sort(key=vertex_priority)
            for vertex in component:
                if vertex in order:
                    continue
                visited, order = dfs(vertex, visited, order)

        for vertex in self.__graph:
            assert vertex in order, "Missing some vertices in topological sort"

        return order

    def is_connected(self, source: Vertex, destination: Vertex) -> bool:
        visited = []
        queue = [source]
        while queue:
            current = queue.pop()
            if current in visited:
                continue
            if current == destination:
                return True
            visited.append(current)
            queue.extend(self.__graph[current])
        return False

    def is_merging_make_a_cycle(self, vertex1: Vertex, vertex2: Vertex)-> bool:
        # temporary removing edges
        v1_to_v2 = vertex2 in self.__graph[vertex1]
        v2_to_v1 = vertex1 in self.__graph[vertex2]
        if v1_to_v2:
            self.__graph[vertex1].remove(vertex2)
        if v2_to_v1:
            self.__graph[vertex2].remove(vertex1)
        
        #check cycle formation
        becomes_a_cycle = (   self.is_connected(vertex1, vertex2)
                           or self.is_connected(vertex2, vertex1))
        # reverting back the removed edges
        if v1_to_v2:
            self.__graph[vertex1].add(vertex2)
        if v2_to_v1:
            self.__graph[vertex2].add(vertex1)

        return becomes_a_cycle

    def clone(self) -> Tuple['Graph[Vertex]', Dict[Vertex, Vertex]]:
        """Clones the current graph

        This function makes a copy of the current graph and returns the
        new graph and the mapping from old vertices to new ones. 
        """
        shallow_copy = Graph()
        mapping = {v: copy.copy(v) for v in self.__graph}
        for vertex, neighbors in self.__graph.items():
            shallow_copy.__graph[mapping[vertex]] = {mapping[n]
                                                     for n in neighbors}
        return shallow_copy, mapping

    def merge(self, main: Vertex, other: Vertex):
        adjacencies = self.__graph[main]
        for destination in self.__graph[other]:
            if destination != main:
                adjacencies.add(destination)
        del self.__graph[other]
        for source, adjacencies in self.__graph.items():
            if source == main:
                adjacencies.discard(other)
                continue
            if other in adjacencies:
                adjacencies.remove(other)
                adjacencies.add(main)
        return self