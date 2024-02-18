from typing import List
from abc import ABC, abstractmethod


class AbstractNode(ABC):
    @abstractmethod
    def __hash__(self) -> int:
        raise NotImplementedError
    
    @abstractmethod
    def __eq__(self, __o: 'AbstractNode') -> bool:
        raise NotImplementedError

    @abstractmethod
    def __lt__(self, __o: 'AbstractNode') -> bool:
        raise NotImplementedError

    @abstractmethod
    def neighbors(self) -> List['AbstractNode']:
        raise NotImplementedError

    @abstractmethod
    def should_be_pruned(self, __o:'AbstractNode') -> bool:
        return False