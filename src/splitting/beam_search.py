from typing import List, Set, TypeVar
from time import time
# from .abstract_node import AbstractNode
from .areces_node import ArecesNode


# Node = TypeVar('Node', bound=AbstractNode)
Node = TypeVar('Node', bound=ArecesNode)


def beam_search(starting_node: Node, width: int, timeout: float) -> Node:
    """ Finds the locally best node, by using beam search algorithm

    Staring from `starting_node`, this function explores the reachable
    nodes to find the best possible one, by following (expanding) only
    the most promising nodes.
    """
    candidates: List[Node] = [starting_node]
    best_node = starting_node
    starting_time = time()
    while candidates and candidates[0].is_promising(best_node):
        best_node = candidates[0]
        # if time() - starting_time > timeout:
        #     break
        new_candidates: List[Node] = []
        for candidate in candidates:
            for neighbor in candidate.neighbors():
                new_candidates.append(neighbor)
        new_candidates.sort()
        candidates = new_candidates[:width]
    return best_node
