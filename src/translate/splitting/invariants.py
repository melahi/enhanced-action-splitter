# Finding invariants based on Rintanen's  paper:
# 'Schematic Invariants by Reduction to Ground Invariants'

from typing import Dict, List, Tuple, Iterable, Optional
from abc import ABC, abstractmethod
from itertools import chain

from pddl import Task, Action, Effect, Predicate, Literal, TypedObject
from pddl.conditions import JunctorCondition, QuantifiedCondition
from pddl.conditions import ConstantCondition

from .common import is_variable


N = 2  # Maximum size of disjunctive invariants


def find_invariants(task: Task):
    pass


class __AbstractType(ABC):
    def __init__(self):
        self.__parent: Optional['__AbstractType'] = None
        self.__children: List['__AbstractType'] = list()
        self.__domain: List[TypedObject]= list()

    @property
    @abstractmethod
    def name(self):
        pass

    @property
    def parent(self):
        return self.__parent

    @property
    def children(self):
        return self.__children.copy()

    @property
    def domain(self):
        # NOTE: The order is important; the first elements should be
        #       the element of its own exclusive members, then we can
        #       have the elements of its children.
        return (  self.__domain
                + list(chain.from_iterable(c.domain for c in self.__children)))

    def add_parent(self, parent: '__AbstractType'):
        if self.__parent is None:
            self.__parent = parent
            parent.__children.append(self)
            return self
        assert self.__parent == parent,  ("`self.__parent` is initialized "
                                          "with a different parent")
        return self

    def add_to_domain(self, objects: List[TypedObject]):
        unused_objects = []
        for object in objects:
            if object.type_name == self.name:
                self.__domain.append(object)
            else:
                unused_objects.append(object)
        for child in self.__children:
            unused_objects = child.add_to_domain(unused_objects)
        return unused_objects

    def _domain_size(self):
        return (  sum(child._domain_size() for child in self.__children)
                + len(self.__domain))


class __Type(__AbstractType):
    def __init__(self, name: str):
        self.__name = name

    @property
    def name(self):
        return self.__name


class __LimitedType(__AbstractType):
    def __init__(self,
                 original_type: __Type,
                 parent: Optional['__LimitedType'],
                 objects_needed: Dict[str, int]):
        self.__type = original_type
        self.add_parent(parent)
        children = [__LimitedType(child,
                                  self,
                                  objects_needed)
                    for child in original_type.children]
        new_objects_needed = self._domain_size() - objects_needed[self.name]
        if new_objects_needed > 0:
            self.add_to_domain(original_type.domain[:new_objects_needed])

    @property
    def name(self):
        return self.__type.name


def __get_max_objects_needed_for_actions(actions: Iterable[Action]):
    def get_constants_in_formula(formula):
        if isinstance(formula, Literal):
            return {a for a in formula.args if not is_variable(a)}
        if isinstance(formula, (JunctorCondition, QuantifiedCondition)):
            return set().union(get_constants_in_formula(p)
                               for p in formula.parts)
        if isinstance(formula, ConstantCondition):
            return set()
        raise NotImplementedError(f"Unknown condition type: {type(formula)}")
    def get_constants_in_effect(effect):
        if isinstance(effect, Effect):
            return (  get_constants_in_formula(effect.condition)
                    + get_constants_in_formula(effect.literal))
        raise NotImplementedError(f"Unknown effect type: {type(effect)}")
    def get_constants(action: Action):
        return (  get_constants_in_formula(action.precondition)
                + set().union(get_constants_in_effect(e)
                              for e in action.effects))

    max_objects_for_actions = dict()
    constants = set()
    for action in actions:
        counter = dict()
        constants_in_action = get_constants(action)
        for symbol in constants_in_action.union(action.parameters):
            counter[symbol.type_name] = counter(symbol.type_name, 0) + 1
        for type_name, count in counter.items():
            max_objects_for_actions[type_name] =\
                max(max_objects_for_actions.get(type_name, 0), count)
        constants.update(constants_in_action)
    return max_objects_for_actions, constants

def __get_max_objects_needed_for_predicates(predicates: Iterable[Predicate]):
    max_objects_for_predicates = dict()
    for predicate in predicates:
        counter = dict()
        for arg in predicate.arguments:
            counter[arg.type_name] = counter.get(arg.type_name, 0) + 1
        for type_name, count in counter.items():
            max_objects_for_predicates[type_name] =\
                max(max_objects_for_predicates.get(type_name, 0), count)
    return max_objects_for_predicates