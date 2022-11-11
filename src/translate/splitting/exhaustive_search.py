from typing import Set, Optional, NewType
from abstract_node import AbstractNode


Node = NewType('Node', AbstractNode)


def exhaustive_search(starting_node: Node) -> Node:
    visited: Set[Node] = set()
    best: Optional[Node] = None
    def dfs(node: Node):
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
    
