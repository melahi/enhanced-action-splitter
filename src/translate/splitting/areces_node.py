from typing import List, Dict, Set
from itertools import combinations

from splitting.abstract_node import AbstractNode

from .abstract_node import AbstractNode
from .graph import Graph
from .micro_action import MicroAction


class ArecesNode(AbstractNode):
    GAMMA = 0
    max_split_size: int
    max_interface_size: int

    @classmethod
    def prepare_class_variables(cls, max_split_size, max_interface_size):
        cls.max_split_size = max_split_size
        cls.max_interface_size = max_interface_size
        return cls
    
    def __init__(self, graph: Graph[MicroAction], overlap: float):
        self.__graph = graph
        self.__key = tuple(sorted((tuple(sorted(p.to_string('')
                                                for p in m.preconditions)),
                                   tuple(sorted(t.to_string('')
                                                for t in m.transitions)))
                                  for m in graph.vertices))

        self.__overlap = overlap
        self.__cost = None

    def __hash__(self) -> int:
        return hash(self.__key)

    def __eq__(self, __o: 'ArecesNode') -> bool:
        return self.__key == __o.__key

    def __lt__(self, __o: 'ArecesNode') -> bool:
        return self.__calculate_cost() < __o.__calculate_cost()

    @property
    def cost(self):
        return self.__calculate_cost()
    
    def neighbors(self) -> List['ArecesNode']:
        result = list()
        for v1, v2 in combinations(self.__graph.vertices, r=2):
            if self.__graph.is_merging_make_a_cycle(v1, v2):
                continue
            new_graph, mapping = self.__graph.clone()
            new_graph.merge(mapping[v1], mapping[v2])
            mapping[v1].merge(mapping[v2])
            overlap = len(v1.args & v2.args) / (1e-9 + len(v1.args | v2.args))  # Adding epsilon to prevent division by zero
            result.append(ArecesNode(new_graph, overlap))
        return result

    def ordered_micro_actions(self):
        return self.__graph.topological_order(lambda v: len(v.preconditions))
    
    def should_be_pruned(self, __o: 'ArecesNode') -> bool:
        return False
    
    def is_promising(self, previous_best: 'ArecesNode') -> bool:
        return self.cost[0] <= previous_best.cost[0]

    def __calculate_cost(self):
        if self.__cost is not None:
            return self.__cost
        split_size = len(self.__graph.vertices)
        normalized_split_size = split_size / self.max_split_size
        interface_size = max([len(m.args) for m in self.__graph.vertices])
        normalized_interface_size = interface_size / self.max_interface_size
        cost1 = (       self.GAMMA  * normalized_split_size
                 + (1 - self.GAMMA) * normalized_interface_size)
        self.__cost = (cost1, -self.__overlap)
        return self.__cost