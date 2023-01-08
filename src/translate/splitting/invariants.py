# Finding invariants based on Rintanen's  paper (2017):
# 'Schematic Invariants by Reduction to Ground Invariants'

from typing import Dict, List, Set, Tuple, Iterable, Optional
from abc import ABC, abstractmethod
from itertools import chain, count, combinations, product
from copy import deepcopy

from pddl import Task, Action, Effect, Predicate, Literal, Atom, TypedObject
from pddl import Type, Conjunction, Truth
from pddl.conditions import JunctorCondition, QuantifiedCondition
from pddl.conditions import ConstantCondition

from .common import is_variable, get_conditions


N = 2  # Maximum size of disjunctive invariants; the name is got from the paper


def find_distinct_args(task: Task) -> Dict[str, Dict[str, List[str]]]:
    """Finds distinct arguments of actions

    Arguments of an action with the same type might not be possible to
    instantiate with the same value. This is a valuable information
    might be helpful for splitting actions. This function find those
    arguments for each action.
    
    The return value is a dictionary from action name to another
    dictionary, which maps the arguments to the list their distinct
    values.

    For example, for an action with name 'a', if we know its argument
    "?x" is distinct with the arguments "?y" and "?z", then we'll have:
    `find_distinct_args(task)['a']['?x'] == ['?y', '?z']`
    """
    if not __is_domain_supported(task):
        # Return a non-restricting output
        return {a: {p.name: [] for p in a.parameters} for a in task.actions}
    __create_limited_instance(task)
    exit(-1)
    types = __construct_types(task.types, task.objects)
    init = {l for l in task.init if isinstance(l, Atom)}
    predicates = [p for p in task.predicates if p.name != "="]
    for invariant in __find_schematic_invariants_in_initial_state(init,
                                                                  predicates,
                                                                  types):
        print(invariant)
    exit(-1)


def __is_domain_supported(task: Task):
    for requirement in task.requirements.requirements:
        if requirement == ":adl":
            return False
        if requirement == ":conditional-effects":
            return False
    return True


class __AbstractType(ABC):
    def __init__(self):
        self.__parent: Optional['__AbstractType'] = None
        self.__children: List['__AbstractType'] = list()
        self.__domain: List[str]= list()

    def __str__(self):
        elements = ", ".join(e.name for e in self.__domain)
        parent_name = "" if self.__parent is None else f"({self.__parent.name})"
        return f"{self.name}{parent_name}: {elements}"

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
        if parent is None:
            return self
        if self.__parent is None:
            self.__parent = parent
            parent.__children.append(self)
            return self
        assert self.__parent == parent,  ("`self.__parent` is initialized "
                                          "with a different parent")
        return self

    def is_subtype(self, type_name: str):
        if self.name == type_name:
            return True
        if self.parent is None:
            return False
        return self.parent.is_subtype(type_name)

    def add_to_domain(self, objects: List[TypedObject]):
        unused_objects = []
        for object in objects:
            if object.type_name == self.name:
                self.__domain.append(object.name)
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
        super().__init__()
        self.__name = name

    @property
    def name(self):
        return self.__name


class __LimitedType(__AbstractType):
    def __init__(self,
                 original_type: '__Type',
                 parent: Optional['__LimitedType'],
                 needed_constants: List[TypedObject],
                 objects_needed: Dict[str, int]):
        super().__init__()
        self.__type = original_type
        self.add_parent(parent)
        for child in original_type.children:
            self.__class__(child, self, needed_constants, objects_needed)
        self.add_to_domain([c
                            for c in needed_constants
                            if c.name == self.name])
        new_objects_needed = objects_needed[self.name] - self._domain_size()
        if new_objects_needed > 0:
            domain = self.domain
            new_elements = [TypedObject(e, self.__type.name)
                            for e in original_type.domain
                            if e not in domain]
            self.add_to_domain(new_elements[:new_objects_needed])

    @property
    def name(self):
        return self.__type.name


def __construct_types(pddl_types: List[Type], objects: List[TypedObject]):
    types: Dict[str, __Type] = {t.name: __Type(t.name) for t in pddl_types}
    root_type = None
    for _type in pddl_types:
        if _type.basetype_name is None:
            assert root_type is None, "Multiple Root types!"
            root_type = types[_type.name]
        else:
            types[_type.name].add_parent(types[_type.basetype_name])
    root_type.add_to_domain(objects)
    return types


def __get_max_objects_needed_for_actions(actions: Iterable[Action]):
    def get_constants_in_formula(formula):
        if isinstance(formula, Literal):
            return {a for a in formula.args if not is_variable(a)}
        if isinstance(formula, (JunctorCondition, QuantifiedCondition)):
            return set().union(*(get_constants_in_formula(p)
                                 for p in formula.parts))
        if isinstance(formula, ConstantCondition):
            return set()
        raise NotImplementedError(f"Unknown condition type: {type(formula)}")
    def get_constants_in_effect(effect):
        if isinstance(effect, Effect):
            return (  get_constants_in_formula(effect.condition)
                    | get_constants_in_formula(effect.literal))
        raise NotImplementedError(f"Unknown effect type: {type(effect)}")
    def get_constants(action: Action):
        return (  get_constants_in_formula(action.precondition)
                | set().union(*(get_constants_in_effect(e)
                                for e in action.effects)))

    max_objects_for_actions = dict()
    constants = set()
    for action in actions:
        counter = dict()
        constants_in_action = get_constants(action)
        constants_in_action = {c.name if isinstance(c, TypedObject) else c
                               for c in constants_in_action}
        for symbol in constants_in_action.union(action.parameters):
            counter[symbol.type_name] = counter.get(symbol.type_name, 0) + 1
        for type_name, count in counter.items():
            max_objects_for_actions[type_name] =\
                max(max_objects_for_actions.get(type_name, 0), count)
        constants.update(constants_in_action)
    return max_objects_for_actions, constants

def __get_max_objects_needed_for_predicates(predicates: Iterable[Predicate]):
    max_objects_for_predicates = dict()
    for predicate in predicates:
        if predicate.name == "=":
            continue
        counter = dict()
        for arg in predicate.arguments:
            counter[arg.type_name] = counter.get(arg.type_name, 0) + 1
        for type_name, count in counter.items():
            max_objects_for_predicates[type_name] =\
                max(max_objects_for_predicates.get(type_name, 0), count)
    return max_objects_for_predicates

def __get_max_objects_needed(task: Task):
    for_predicates = __get_max_objects_needed_for_predicates(task.predicates)
    for_actions, constants = __get_max_objects_needed_for_actions(task.actions)
    constants = [obj for obj in task.objects if obj.name in constants]
    for t in task.types:
        for_predicates.setdefault(t.name, 0)
        for_actions.setdefault(t.name, 0)
    # Calculating the formula $L_t^N(A, P)$
    L = {t.name: (  max(for_actions[t.name], for_predicates[t.name])
                  + (N - 1) * for_predicates[t.name])
         for t in task.types}
    return constants, L


__global_variable_counter = count()
def get_new_global_variable():
    global __global_variable_counter
    return get_variable(next(__global_variable_counter))
def get_variable(index):
    return f"?var_{index}"
def get_new_atom(predicate: Predicate):
    return Atom(predicate.name, (TypedObject(get_new_global_variable(),
                                             arg.type_name)
                                 for arg in predicate.arguments))


class __SchematicInvariant:
    # Schematic of the form $[(v_i != v_j)/\...] -> [P(v_1, ..., v_n) \/ ...]$
    def __init__(self,
                 inequalities: List[Tuple[str, str]],
                 disjunction: List[Literal]):
        # normalizing names to our local namespace
        local_ids = dict()
        disjunction = deepcopy(disjunction)
        disjunction.sort(key=str)
        for literal in disjunction:
            for arg in literal.args:
                id = local_ids.setdefault(arg.name, len(local_ids))
                arg.name = get_variable(id)
        self.__disjunction = tuple(disjunction)
        inequalities = [(get_variable(local_ids[v1]),
                         get_variable(local_ids[v2]))
                        for v1, v2 in inequalities]
        inequalities = {(v2, v1) if v2 < v1 else (v1, v2)
                        for v1, v2 in inequalities}
        inequalities = sorted(inequalities)
        self.__inequalities = tuple(inequalities)

    def __hash__(self):
        return hash(tuple((self.__disjunction, self.__inequalities)))

    def __eq__(self, __o: '__SchematicInvariant') -> bool:
        return (    self.__disjunction == __o.__disjunction
                and self.__inequalities == __o.__inequalities)

    def __str__(self):
        inequalities = [f'({v1} != {v2})' for v1, v2 in self.__inequalities]
        disjunction = [str(l) for l in self.__disjunction]
        return f"{' and '.join(inequalities)} -> {r' or '.join(disjunction)}"

    def weaken(self,
               predicates: List[Predicate],
               types: Dict[str, '__AbstractType']):
        weakened_invariants: List['__SchematicInvariant'] = []
        if len(self.__disjunction) < N:
            for predicate in predicates:
                atom = get_new_atom(predicate)
                for literal in [atom, atom.negate()]:
                    invariant = self.__class__(self.__inequalities,
                                               [*self.__disjunction, literal])
                    weakened_invariants.append(invariant)
        for i, j in combinations(range(len(self.__disjunction)), r=2):
            for k, l in product(range(len(self.__disjunction[i].args)),
                                range(len(self.__disjunction[j].args))):
                disjunction = list(deepcopy(m) for m in self.__disjunction)
                arg1: TypedObject = disjunction[i].args[k]
                arg2: TypedObject = disjunction[j].args[l]
                if arg1.name == arg2.name:
                    continue
                if (   (arg1.name, arg2.name) in self.__inequalities
                    or (arg2.name, arg1.name) in self.__inequalities):
                    continue
                if types[arg1.type_name].is_subtype(arg2.type_name):
                    new_args = tuple(a if m != k else deepcopy(arg2)
                                     for m,a in enumerate(disjunction[i].args))
                    disjunction[i].args = new_args
                    inequalities = [(v1 if v1 != arg1.name else arg2.name,
                                     v2 if v2 != arg1.name else arg2.name)
                                    for v1, v2 in self.__inequalities]
                elif types[arg2.type_name].is_subtype(arg1.type_name):
                    new_args = tuple(a if m != l else deepcopy(arg1)
                                     for m,a in enumerate(disjunction[j].args))
                    disjunction[j].args = new_args
                    inequalities = [(v1 if v1 != arg2.name else arg1.name,
                                     v2 if v2 != arg2.name else arg1.name)
                                    for v1, v2 in self.__inequalities]
                else:
                    continue
                # Creating a new weakened invariant by adding an equality
                # constraint for two variables
                invariant = self.__class__(inequalities, disjunction)
                weakened_invariants.append(invariant)
                # Creating another weakened invariant by adding an
                # inequality constraint for two variables
                invariant = self.__class__([*self.__inequalities,
                                            (arg1.name, arg2.name)],
                                           list(self.__disjunction))
                weakened_invariants.append(invariant)
        return weakened_invariants

    def instantiate(self, types: Dict[str, '__AbstractType']):
        args = {a.name: types[a.type_name]
                for l in self.__disjunction
                for a in l.args}
        for instance in product(*(t.domain for _, t in args.items())):
            values = {n: v for n, v in zip(args.keys(), instance)}
            for v1, v2 in self.__inequalities:
                if values[v1] == values[v2]:
                    break
            else:
                disjunction = deepcopy(self.__disjunction)
                for literal in disjunction:
                    literal.args = tuple(values[a.name] for a in literal.args)
                yield disjunction


def __find_schematic_invariants_in_initial_state(initial_state: Set[Atom],
                                                 predicates: List[Predicate],
                                                 types: Dict[str, __Type]):
    def is_valid(invariant: __SchematicInvariant):
        for ground_invariant in invariant.instantiate(types):
            for literal in ground_invariant:
                if isinstance(literal, Atom):
                    if literal in initial_state:
                        break
                else:
                    if literal.negate() not in initial_state:
                        break
            else:
                return False
        return True

    candidates = __SchematicInvariant([], []).weaken(predicates, types)
    invariants: List[__SchematicInvariant] = list()
    visited = set()
    while candidates:
        candidate_invariant = candidates.pop()
        if candidate_invariant in visited:
            continue
        visited.add(candidate_invariant)
        if is_valid(candidate_invariant):
            invariants.append(candidate_invariant)
        else:
            candidates.extend(candidate_invariant.weaken(predicates, types))
    return invariants

def __ground_action(action: Action, types: Dict[str, '__AbstractType']):
    grounded_actions: List[Action] = list()
    for values in product(*(types[p.type_name].domain
                            for p in action.parameters)):
        mappings = {p.name: v for p, v in zip(action.parameters, values)}
        preconditions = [c.rename_variables(mappings)
                         for c in get_conditions(action.precondition)]
        effects = [Effect(e.parameters,
                          Conjunction([c.rename_variables(mappings)
                                       for c in get_conditions(e.condition)]),
                          e.literal.rename_variables(mappings))
                   for e in action.effects]
        parameters = [TypedObject(mappings[p.name], p.type_name)
                      for p in action.parameters]
        grounded_actions.append(Action(action.name,
                                       parameters, 
                                       action.num_external_parameters,
                                       Conjunction(preconditions),
                                       effects,
                                       action.cost))
    return grounded_actions

def __find_root(types: Dict[str, __AbstractType]):
    root = None
    for _type in types.values():
        if _type.parent is None:
            assert root is None,  "Multi Root type!"
            root = _type
    return root

def __get_all_limited_types(root: __LimitedType):
    def get_types(_type:__LimitedType, all_types: Dict[str, __LimitedType]):
        for child in _type.children:
            all_types = get_types(child, all_types)
        all_types[_type.name] = _type
        return all_types
    return get_types(root, dict())

def __create_limited_instance(task: Task):
    constants, objects_needed = __get_max_objects_needed(task)
    types = __construct_types(task.types, task.objects)
    root_type = __find_root(types)
    root_limited_type = __LimitedType(root_type,
                                      None,
                                      constants,
                                      objects_needed)
    limited_types = __get_all_limited_types(root_limited_type)
    ground_actions = []
    for action in task.actions:
        ground_actions.extend(__ground_action(action, limited_types))
    for action in ground_actions:
        print("=========================")
        print(action)