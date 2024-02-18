import gc
from time import time
from typing import List, Dict, Optional, TypeVar
from random import randrange, random

from .abstract_node import AbstractNode


EPSILON = 0.001  # The probability of choosing a random child, otherwise
                 # we select the best child (p(best child) = 1 - EPSILON).


Node = TypeVar('Node', bound=AbstractNode)


def random_walk(starting_node: Node, timeout: float) -> Node:
    graph: Dict[Node, List[Node]] = dict()
    best: Optional[Node] = None
    def walk(node: Node):
        nonlocal best
        first_time_visited = False
        if node not in graph:
            if best is not None and node.should_be_pruned(best):
                graph[node] = []
                return True
            first_time_visited = True
            neighbors = node.neighbors()
            neighbors.sort()
            graph[node] = neighbors
            if not neighbors:
                if best is None or node < best:
                    best = node
                return True
        elif node.should_be_pruned(best):  # We know `best` is not None
            return False
        neighbors = graph[node]  # `neighbors` is a sorted list
        while neighbors:
            neighbors_count = len(neighbors)
            if first_time_visited or random() > EPSILON:
                neighbors_count = 1
                for i in range(1, len(neighbors)):
                    if neighbors[0] < neighbors[i]:
                        break
                    # else neighbor[0] == neighbors[i]
                    neighbors_count += 1
            index = randrange(neighbors_count)
            if walk(neighbors[index]):
                return True
            neighbors.pop(index)
        return False
    print("Start random walk:")
    iteration = 0
    starting_time = time()
    while time() - starting_time <= timeout:
        iteration += 1
        if iteration % 1000 == 0:
            print("Iteration:", iteration, flush=True)
        if not walk(starting_node):
            print(f"All search space is explored in iteration: {iteration}")
            break

    del graph
    gc.collect()
    return best
