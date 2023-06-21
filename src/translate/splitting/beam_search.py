from typing import List, Set, TypeVar
# from .abstract_node import AbstractNode
from .areces_node import ArecesNode


# Node = TypeVar('Node', bound=AbstractNode)
Node = TypeVar('Node', bound=ArecesNode)


def beam_search(starting_node: Node, width: int) -> Node:
    """ Finds the locally best node, by using beam search algorithm

    Staring from `starting_node`, this function explores the reachable
    nodes to find the best possible one, by following (expanding) only
    the most promising nodes.
    """

    visited: Set[Node] = {starting_node}
    expanded: Set[Node] = set()
    candidates: List[Node] = [starting_node]
    best_node = starting_node
    while candidates and candidates[0].is_promising(best_node):
        best_node = candidates[0]
        new_candidates: List[Node] = []
        for candidate in candidates:
            if candidate in expanded:
                continue
            for neighbor in candidate.neighbors():
                if neighbor in visited:
                    continue
                visited.add(neighbor)
                new_candidates.append(neighbor)
            expanded.add(candidate)
        new_candidates.sort()
        candidates = new_candidates[:width]
    return best_node