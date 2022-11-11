from typing import List, Set, NewType
from abstract_node import AbstractNode


Node = NewType('Node', AbstractNode)


def beam_search(starting_node: Node, width: int) -> Node:
    """ Finds the locally best node, by using beam search algorithm

    Staring from `starting_node`, this function explores the reachable
    nodes to find the best possible one, by following (expanding) only
    the most promising nodes.
    """

    visited: Set[Node] = {starting_node}
    expanded: Set[Node] = set()
    candidates: List[Node] = [starting_node]
    level_off = False
    while not level_off:
        level_off = True
        for candidate in candidates.copy():
            if candidate in expanded:
                continue
            for neighbor in candidate.neighbors():
                if neighbor in visited:
                    continue
                visited.add(neighbor)
                candidates.append(neighbor)
            level_off = False
            expanded.add(candidate)
        candidates.sort()
        candidates = candidates[:width]
    return candidates[0]