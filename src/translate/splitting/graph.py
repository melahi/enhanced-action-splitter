from typing import List, Tuple, Generic, TypeVar


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
        self.__graph = {vertex: [] for vertex in vertices}

    def __str__(self) -> str:
        return str(self.__graph)

    @property
    def vertices(self):
        return [*self.__graph]

    def add_edge(self, edge: Tuple[Vertex, Vertex]):
        source, destination = edge
        self.__graph.setdefault(source, []).append(destination)
        return self

    def neighbors(self, vertex: Vertex):
        return self.__graph[vertex].copy()

    def topological_order(self, vertex_priority=None) -> List[Vertex]:
        def dfs(vertex, visited, order):
            stack = [(False, vertex)]
            while stack:
                completed, vertex = stack.pop()
                if completed:
                    order = [vertex] + order
                    continue
                if vertex in visited:
                    continue
                visited.append(vertex)
                neighbors = self.__graph[vertex]
                if vertex_priority:
                    neighbors.sort(key=vertex_priority, reverse=True)
                stack.append((True, vertex))
                stack.extend([(False, n) for n in neighbors])
            return visited, order

        order = []
        visited = []
        vertices = self.__graph
        if vertex_priority:
            vertices = sorted(vertices, key=vertex_priority)
        for vertex in vertices:
            if vertex not in order:
                visited, order = dfs(vertex, visited, order)

        return order

    def is_connected(self, source: Vertex, destination: Vertex) -> bool:
        visited = []
        queue = [source]
        while not queue:
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
            self.__graph[vertex1].append(vertex2)
        if v2_to_v1:
            self.__graph[vertex2].append(vertex1)

        return becomes_a_cycle

    def merge(self, main: Vertex, other: Vertex):
        adjacencies = self.__graph[main]
        for destination in self.__graph[other]:
            if destination != main and destination not in adjacencies:
                adjacencies.append(destination)
        del self.__graph[other]
        for source, adjacencies in self.__graph.items():
            if source == main:
                if other in adjacencies:
                    adjacencies.remove(other)
                continue
            for i in range(len(adjacencies)):
                if adjacencies[i] == other:
                    adjacencies[i] = main
        return self