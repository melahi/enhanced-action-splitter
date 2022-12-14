from time import time
from typing import List, Dict, Optional, TypeVar
from random import randrange

from .abstract_node import AbstractNode


Node = TypeVar('Node', bound=AbstractNode)


def random_walk(starting_node: Node, timeout: float) -> Node:
    graph: Dict[Node, List[Node]] = dict()
    best: Optional[Node] = None
    def walk(node: Node):
        nonlocal best
        if node not in graph:
            neighbors = node.neighbors()
            graph[node] = neighbors
            if not neighbors:
                if best is None or node < best:
                    best = node
                return True
        neighbors = graph[node]
        while neighbors:
            index = randrange(len(neighbors))
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
            print("Iteration:", iteration)
        if not walk(starting_node):
            print(f"All search space is explored in iteration: {iteration}")
            break

    return best