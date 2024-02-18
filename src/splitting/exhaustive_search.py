from typing import Set, Optional, TypeVar
from .abstract_node import AbstractNode


Node = TypeVar('Node', bound=AbstractNode)


def exhaustive_search(starting_node: Node) -> Node:
    visited: Set[Node] = set()
    best: Optional[Node] = None
    def dfs(node: Node):
        nonlocal best
        if node in visited:
            return
        visited.add(node)
        neighbors = node.neighbors()
        if not neighbors:
            # `node` is a terminal node
            if best is None or node < best:
                best = node
            return
        for neighbor in neighbors:
            dfs(neighbor)
    dfs(starting_node)
    return best
    
