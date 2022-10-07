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
        for vertex in self.__graph:
            if vertex not in order:
                visited, order = dfs(vertex, visited, order)

        return order