# Finding invariants based on Rintanen's  paper (2017):
# 'Schematic Invariants by Reduction to Ground Invariants'

from typing import Dict, List, Set, Tuple, Iterable, Optional
from abc import ABC, abstractmethod
from itertools import chain, count, combinations, product
from functools import cmp_to_key, reduce

from pddl import Task, Action, Effect, Predicate, Literal, Atom, TypedObject
from pddl import Type, Conjunction, NegatedAtom
from pddl.conditions import JunctorCondition, QuantifiedCondition
from pddl.conditions import ConstantCondition

from .common import is_variable, get_conditions
from .sat_solver import Context


N = 2  # Maximum size of disjunctive invariants; the name is got from the paper
MAX_GROUND_SIZE = 10000
MAX_INVARIANT_SCHEMA_SIZE = 10000


class ArgExpert:
    def __init__(self,
                 distinct_args: Dict[str, Dict[str, Set[str]]],
                 actions: List[Action],
                 types: Dict[str, '__LimitedType'],
                 invariants: List[List[Literal]]):
            self.__distinct_args = distinct_args
            self.__parameters = {a.name: {p.name: p.type_name
                                          for p in a.parameters}
                                 for a in actions}
            self.__types = types
            self.__context = Context()
            for invariant in invariants:
                self.__context.add_clause(invariant)
            self.__context.add_scope()
            # Memoizing if two literals are equivalent, given a set
            # of conditions.
            self.__memoized: Dict[Tuple(Tuple[str, ...], Tuple[Literal, ...]),
                                  bool] = dict()

    def are_distinct(self,
                     action_name: str,
                     literal1: Literal,
                     literal2: Literal,
                     conditions: List[Literal]):
        if conditions is None:
            # Two literals are in effects, so we can use our general
            # information: `self.__distinct_args`
            distinct_args = self.__distinct_args[action_name]

            # we assume the predicate names of two literal has already
            # been checked.
            for arg1, arg2 in zip(literal1.args, literal2.args):
                if arg1 in distinct_args[arg2]:
                    return True
            return False

        replacing_args: Dict[TypedObject, TypedObject] = {}
        for arg1, arg2 in zip(literal1.args, literal2.args):
            arg1 = replacing_args.setdefault(arg1, arg1)
            arg2 = replacing_args.setdefault(arg2, arg2)
            if not is_variable(arg1):
                replacing_args[arg2] = arg1
                continue
            if not is_variable(arg2):
                replacing_args[arg1] = arg2
                continue
            arg1_type = self.__parameters[action_name][arg1]
            arg2_type = self.__parameters[action_name][arg2]
            if self.__types[arg1_type].is_subtype(arg2_type):
                replacing_args[arg2] = arg1
            else:
                replacing_args[arg1] = arg2

        new_args, conditions = self.__normalize_conditions(
            conditions, self.__parameters[action_name], replacing_args)
        result = not self.__are_satisfiable(new_args, conditions)
        return result

    def __normalize_conditions(self,
                              condition: List[Literal],
                              arg_types: Dict[str, '__LimitedType'],
                              replacing_args: Dict[str, str]):
        new_args: List[TypedObject] = []
        args_mapping: Dict[str, str] = dict()
        for arg1, arg2 in replacing_args.items():
            if arg2 not in args_mapping:
                if is_variable(arg2):
                    new_args.append(TypedObject(get_variable(len(new_args)),
                                                arg_types[arg2]))
                    args_mapping[arg2] = new_args[-1].name
                else:
                    args_mapping[arg2] = arg2
            args_mapping[arg1] = args_mapping[arg2]
        normalized_condition: List[Literal] = []
        for literal in sorted(condition, key=str):
            literal_args = []
            for arg in literal.args:
                if not is_variable(arg):
                    literal_args.append(arg)
                    continue
                if arg not in args_mapping:
                    new_args.append(TypedObject(get_variable(len(new_args)),
                                                arg_types[arg]))
                    args_mapping[arg] = new_args[-1].name
                literal_args.append(args_mapping[arg])
            new_literal = literal.__class__(literal.predicate, literal_args)
            normalized_condition.append(new_literal)
        return new_args, tuple(normalized_condition)

    def __are_satisfiable(self,
                          args: List[TypedObject],
                          conditions: Tuple[Literal]):
        key = (tuple(a.type_name for a in args), conditions)
        if key in self.__memoized:
            return self.__memoized[key]
        action = Action("", args, len(args), Conjunction(conditions), [], 0)
        ground_actions = generate_ground_action(action, self.__types)
        if ground_actions is None:
            # High number of ground actions
            self.__memoized[key] = True
            return True
        for ground_action in ground_actions:
            self.__context.add_scope()
            for condition in get_conditions(ground_action.precondition):
                self.__context.add_clause([condition])
            is_sat = self.__context.is_satisfiable()
            self.__context.drop_scope()
            if is_sat:
                self.__memoized[key] = True
                return True
        self.__memoized[key] = False
        return False


def construct_arg_expert(task: Task) -> ArgExpert:
    """Construct an expert to analysis arguments

    Arguments of an action with the same type might not be possible to
    instantiate with the same value. This is a valuable information
    might be helpful for splitting actions.
    """
    if True or not __is_domain_supported(task):
        return __get_non_restricting_args(task)
    limited_types = __construct_limited_types(task)
    grounded_actions = __limited_ground_actions(task.actions, limited_types)
    if grounded_actions is None:
        return __get_non_restricting_args(task)
    types = __construct_types(task.types, task.objects)
    init = {l for l in task.init if isinstance(l, Atom)}
    predicates = [p for p in task.predicates if p.name != "="]
    init_invariants = __find_schematic_invariants_in_initial_state(init,
                                                                   predicates,
                                                                   types)
    init_invariants = __ground_invariants(limited_types, init_invariants)
    invariants = __find_invariants(init_invariants, grounded_actions)
    distinct_args = __find_distinct_args(task, invariants, grounded_actions)
    # completed_task = __complete_task(task, types, distinct_args)
    return ArgExpert(distinct_args, task.actions, limited_types, invariants)

def __get_non_restricting_args(task: Task):
    class DummyArgExpert:
        def are_distinct(*args):
            return False
    return DummyArgExpert()

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
        self.__domain: List[TypedObject]= list()

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
        for obj in objects:
            if obj.type_name == self.name:
                self.__domain.append(TypedObject(obj.name, obj.type_name))
            else:
                unused_objects.append(obj)
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
            domain = [e.name for e in self.domain]
            new_elements = [TypedObject(e.name, self.__type.name)
                            for e in original_type.domain
                            if e.name not in domain]
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

def __get_constants(action: Action):
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
    return (  get_constants_in_formula(action.precondition)
            | set().union(*(get_constants_in_effect(e)
                            for e in action.effects)))

def __get_max_objects_needed_for_actions(task: Task):
    actions = task.actions
    objects = task.objects
    def get_type(symbol):
        if isinstance(symbol, TypedObject):
            return symbol.type_name
        for obj in objects:
            if obj.name == symbol:
                return obj.type_name
    max_objects_for_actions = dict()
    constants = set()
    for action in actions:
        counter = dict()
        constants_in_action = __get_constants(action)
        constants_in_action = {c.name if isinstance(c, TypedObject) else c
                               for c in constants_in_action}
        for symbol in constants_in_action.union(action.parameters):
            counter[get_type(symbol)] = counter.get(get_type(symbol), 0) + 1
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
    for_actions, constants = __get_max_objects_needed_for_actions(task)
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
        normalized_disjunction: List[Literal] = []
        for literal in sorted(disjunction, key=str):
            new_args = []
            for arg in literal.args:
                id = local_ids.setdefault(arg.name, len(local_ids))
                new_args.append(TypedObject(get_variable(id), arg.type_name))
            new_literal = literal.__class__(literal.predicate, new_args)
            normalized_disjunction.append(new_literal)
        self.__disjunction = tuple(normalized_disjunction)
        inequalities = [(get_variable(local_ids[v1]),
                         get_variable(local_ids[v2]))
                        for v1, v2 in inequalities]
        inequalities = {(v2, v1) if v2 < v1 else (v1, v2)
                        for v1, v2 in inequalities}
        inequalities = sorted(inequalities)
        self.__inequalities = tuple(inequalities)
        self.__hash = hash((self.__disjunction, self.__inequalities))

    def __hash__(self):
        return self.__hash

    def __eq__(self, __o: '__SchematicInvariant') -> bool:
        return (    self.__hash == __o.__hash
                and self.__disjunction == __o.__disjunction
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
                p, q = i, j
                arg1: TypedObject = self.__disjunction[p].args[k]
                arg2: TypedObject = self.__disjunction[q].args[l]
                if arg1.name == arg2.name:
                    continue
                if (   (arg1.name, arg2.name) in self.__inequalities
                    or (arg2.name, arg1.name) in self.__inequalities):
                    continue
                if types[arg1.type_name].is_subtype(arg2.type_name):
                    arg1, arg2, p, q, k, l = arg2, arg1, q, p, l, k
                elif not types[arg2.type_name].is_subtype(arg1.type_name):
                    continue
                new_arg = TypedObject(arg1.name, arg1.type_name)
                disjunction = [n if m != q else n.replace_argument(l, new_arg)
                               for m, n in enumerate(self.__disjunction)]
                if any(m.negate() == n
                       for m, n in combinations(disjunction, r=2)):
                    continue
                inequalities = [(v1 if v1 != arg2.name else arg1.name,
                                 v2 if v2 != arg2.name else arg1.name)
                                for v1, v2 in self.__inequalities]
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

    def instantiate_size(self, types: Dict[str, '__AbstractType']):
        args = {a.name: types[a.type_name]
                for l in self.__disjunction
                for a in l.args}
        return reduce(lambda x, y: x * y._domain_size(), args.values(), 1)

    def instantiate(self, types: Dict[str, '__AbstractType']):
        args = {a.name: types[a.type_name]
                for l in self.__disjunction
                for a in l.args}
        for instance in product(*(t.domain for _, t in args.items())):
            values = {n: v.name for n, v in zip(args.keys(), instance)}
            for v1, v2 in self.__inequalities:
                if values[v1] == values[v2]:
                    break
            else:
                yield {l.__class__(l.predicate,
                                   [values[a.name] for a in l.args])
                       for l in self.__disjunction}


def __find_schematic_invariants_in_initial_state(initial_state: Set[Atom],
                                                 predicates: List[Predicate],
                                                 types: Dict[str, __Type]):
    def is_valid(invariant: __SchematicInvariant):
        if invariant.instantiate_size(types) > MAX_INVARIANT_SCHEMA_SIZE:
            return False
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

def __weaken_invariant(invariant: Set[Literal], effects: List[Effect]):
    if len(invariant) >= N:
        return []
    # TODO: I should think more about this part, because actions are
    #       not instantiated with all possible values; so, perhaps we
    #       need to consider more general case in weakening an
    #       invariant (or, what we have done might be sufficient).
    not_literal = [l.negate() for l in invariant]
    effects = [e.literal for e in effects]
    return [{*invariant, e} for e in effects if e not in not_literal]

def __find_novel_invariants(existing_invariants: List[Set[Literal]],
                            new_invariants: List[Set[Literal]]):
    new_invariants.sort(key=len)
    novel_invariants: List[Set[Literal]] = list()
    for new_invariant in new_invariants:
        for existing_invariant in existing_invariants + novel_invariants:
            if existing_invariant.issubset(new_invariant):
                break
        else:
            novel_invariants.append(new_invariant)
    return novel_invariants

def __is_possibly_violated(context: Context, 
                           effects: List[Effect],
                           invariant: Set[Literal]):
    not_invariant = [l.negate() for l in invariant]
    for effect in effects:
        if effect.literal in invariant:
            return False
        try:
            not_invariant.remove(effect.literal)
        except ValueError:
            pass
    if len(not_invariant) == len(invariant):
        # These effects don't modify the invariant
        return False

    context.add_scope()
    for literal in not_invariant:
        context.add_clause([literal])
    is_violated = context.is_satisfiable()
    context.drop_scope()
    return is_violated

def __refine_invariants(context: Context,
                        action: Action,
                        invariants: List[Set[Literal]]):
    context.add_scope()
    refined_invariants: List[Set[Literal]] = []
    for condition in get_conditions(action.precondition):
        context.add_clause([condition])
    if not context.is_satisfiable():
        context.drop_scope()
        return False, invariants
    is_modified = False
    while invariants:
        invariant = invariants.pop()
        if __is_possibly_violated(context, action.effects, invariant):
            weakened_invariants = __weaken_invariant(invariant, action.effects)
            invariants.extend(__find_novel_invariants(  refined_invariants
                                                      + invariants,
                                                      weakened_invariants))
            is_modified = True
        else:
            refined_invariants.append(invariant)
    context.drop_scope()
    return is_modified, refined_invariants

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

def __construct_limited_types(task: Task):
    constants, objects_needed = __get_max_objects_needed(task)
    types = __construct_types(task.types, task.objects)
    root_type = __find_root(types)
    root_limited_type = __LimitedType(root_type,
                                      None,
                                      constants,
                                      objects_needed)
    return __get_all_limited_types(root_limited_type)

def generate_ground_action(action: Action, types: Dict[str, __LimitedType]):
    def types_comparison(obj1: TypedObject, obj2: TypedObject):
        if types[obj1.type_name].is_subtype(obj2.type_name):
            return -1
        return int(types[obj2.type_name].is_subtype(obj1.type_name))

    constants = {c.name if isinstance(c, TypedObject) else c
                 for c in __get_constants(action)}
    # Order the parameters so that more general types placed later
    parameters = sorted(action.parameters, key=cmp_to_key(types_comparison))
    domains: List[List[str]] = []
    for i in range(len(parameters)):
        domains.append([])
        for j in range(i):
            if types[parameters[j].type_name].is_subtype(parameters[i]
                                                         .type_name):
                for value in domains[j]:
                    if value not in domains[i]:
                        domains[i].append(value)
                        break
        for obj in types[parameters[i].type_name].domain:
            if obj.name not in domains[i] and obj.name not in constants:
                domains[i].append(obj.name)
                break
    for domain, parameter in zip(domains, parameters):
        for constant in constants:
            if constant in [o.name for o in types[parameter.type_name].domain]:
                domain.append(constant)
    ground_size = reduce(lambda x, y: x * y, [len(d) for d in domains], 1)
    if ground_size > MAX_GROUND_SIZE:
        print(f"Skip grounding {action.name}; size: {ground_size}")
        return None
    grounded_actions: List[Action] = []
    for values in product(*domains):
        mappings = {p.name: v for p, v in zip(parameters, values)}
        preconditions = [c.rename_variables(mappings)
                         for c in get_conditions(action.precondition)]
        effects = [Effect(e.parameters,
                          Conjunction([c.rename_variables(mappings)
                                       for c in get_conditions(e.condition)]),
                          e.literal.rename_variables(mappings))
                   for e in action.effects]
        grounded_parameters = [TypedObject(mappings[p.name], p.type_name)
                               for p in action.parameters]
        grounded_actions.append(Action(action.name,
                                       grounded_parameters, 
                                       action.num_external_parameters,
                                       Conjunction(preconditions),
                                       effects,
                                       action.cost))
    return grounded_actions

def __limited_ground_actions(actions: List[Action],
                             types: Dict[str, __LimitedType]):
    grounded_actions: List[Action] = []
    for action in actions:
        new_grounded_actions = generate_ground_action(action, types)
        if new_grounded_actions is None:
            return None
        grounded_actions.extend(new_grounded_actions)
    return grounded_actions

def __ground_invariants(types: Dict[str, __AbstractType],
                        schematic_invariants: List[__SchematicInvariant]):
    invariants = list(chain(*(i.instantiate(types)
                              for i in schematic_invariants)))
    invariants = __find_novel_invariants([], invariants)
    return invariants

def __find_invariants(init_invariants: List[List[Literal]],
                      grounded_actions: List[Action]):
    invariants = init_invariants
    context = Context()
    level_off = False
    while not level_off:
        level_off = True
        context.add_scope()
        for invariant in invariants:
            context.add_clause(invariant)
        for grounded_action in grounded_actions:
            is_modified, invariants = __refine_invariants(context,
                                                          grounded_action,
                                                          invariants)
            level_off &= not is_modified
        context.drop_scope()
    return invariants

def __find_distinct_args(task: Task,
                         invariants: List[List[Literal]],
                         grounded_actions: List[Action]):
    context = Context()
    for invariant in invariants:
        context.add_clause(invariant)
    def is_applicable(ground_action: Action):
        context.add_scope()
        for precondition in get_conditions(ground_action.precondition):
            context.add_clause([precondition])
        applicable = context.is_satisfiable()
        context.drop_scope()
        return applicable

    parameters = {a.name: a.parameters for a in task.actions}
    # We assume all args are distinct, unless we find an applicable ground
    # action that some of its arguments is unified with the same value.
    distinct_args: Dict[str, Dict[str, Set[str]]] = {}
    for action, params in parameters.items():
        for p1 in params:
            for p2 in params:
                if p1.name == p2.name:
                    continue
                (distinct_args
                .setdefault(action, {})
                .setdefault(p1.name, set())
                .add(p2.name))
    
    for action in grounded_actions:
        same_args = []
        for (p1, v1), (p2, v2) in combinations(zip(parameters[action.name],
                                                   action.parameters),
                                               r=2):
            if v1.name == v2.name:
                same_args.append((p1.name, p2.name))
        if same_args and is_applicable(action):
            for p1, p2 in same_args:
                distinct_args[action.name][p1].discard(p2)
                distinct_args[action.name][p2].discard(p1)
    return distinct_args

def __complete_task(task: Task,
                    types: Dict[str, __AbstractType],
                    distinct_args: Dict[str, Dict[str, Set[str]]]):
    """ Adds argument inequalities of actions to their preconditions """
    for action in task.actions:
        preconditions = get_conditions(action.precondition)
        inequalities = [(l.args[0], l.args[1]) for l in preconditions
                        if isinstance(l, NegatedAtom) and l.predicate == "="]
        for p1, p2 in combinations(action.parameters, r=2):
            if p2.name not in distinct_args[action.name][p1.name]:
                continue
            if (   (p1.name, p2.name) in inequalities
                or (p2.name, p1.name) in inequalities):
                continue
            if (set(types[p1.type_name].domain)
                .isdisjoint(types[p2.type_name].domain)):
                continue
            preconditions += [NegatedAtom("=", [p1.name, p2.name])]
        action.precondition = Conjunction(preconditions)
    return task