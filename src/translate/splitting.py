#! /usr/bin/env python3


import os
from typing import List, Dict, Set, Tuple, Iterable, Generic, TypeVar
from itertools import chain, permutations
from functools import reduce

import normalize
import pddl_parser
from sccs import get_sccs_adjacency_dict
from invariant_finder import find_invariants
from invariants import Invariant
import pddl
from pddl.tasks import Task
from pddl.pddl_types import TypedObject
from pddl.effects import ConditionalEffect, Effect, SimpleEffect
from pddl.conditions import Conjunction, Literal, Atom, NegatedAtom, Truth


Predicate = Tuple[str, Iterable[str]]  # predicate type
MAX_ARGUMENTS = 3


class AtomicActionPart:
    def __str__(self):
        return self.to_string(indent="")

    def find_args(self):
        raise NotImplementedError

    def is_threatened_by(self, transition: 'Transition') -> bool:
        raise NotImplementedError

    def to_string(self, indent) -> str:
        raise NotImplementedError

    @staticmethod
    def _find_args_in_literal(literal: Literal):
        return {arg for arg in literal.args if arg.startswith("?")}

    @staticmethod
    def _are_possibly_the_same(literal1: Literal, literal2: Literal) -> bool:
        if literal1.predicate != literal2.predicate:
            return False
        for arg1, arg2 in zip(literal1.args, literal2.args):
            if arg1.startswith("?") or arg2.startswith("?"):
                continue
            if arg1 != arg2:
                return False
        return True


class Condition(AtomicActionPart):
    def __init__(self, condition: Literal):
        self.__condition = condition

    def find_args(self):
        if isinstance(self.__condition, Literal):
            return self._find_args_in_literal(self.__condition)
        raise NotImplementedError("Other Conditions are not supported!")

    def is_threatened_by(self, transition: 'Transition') -> bool:
        for effect in transition.effects:
            if self._are_possibly_the_same(self.__condition, effect):
                return True
        return False

    def to_string(self, indent) -> str:
        return indent + literal_to_string(self.__condition) + "\n"


class Transition(AtomicActionPart):
    def __init__(self,
                 conditions: List[Literal],
                 main_effect: Literal,
                 variables_ids: Set[int]):
        self.__main_effect = main_effect
        self.__conditions = conditions
        self.__variables_ids = variables_ids
        self.__effects = [main_effect]

    def check_delete_effect(self, variables_ids, conditions, del_effect):
        """Updates the transition according to the given delete effect

        Checks if the given delete effect is related to this transition
        or not; if it affects the same state variable as the transition,
        and its condition is logical consequence of the transition's
        conditions, then the delete effect is related to this transition.

        Returns:
            Set[int]: The set of IDs of common state variables
        """
        common_variables_ids = self.__variables_ids.intersection(variables_ids)
        if not common_variables_ids:
            # `del_effect` is not related to this transition
            return set()

        statements = set().union(*self.__conditions,
                                 {self.__main_effect.negate()},
                                 {del_effect.negate()})
        # TODO: We are supposed to check if `condition` is a logical
        #       consequence of `statement` or not. In the following,
        #       for simplicity, I have not used some other knowledge in
        #       action's precondition, the problem itself, or even the
        #       possible unification, so it might be not precise. I
        #       should fix this!
        if statements.issuperset(set(conditions)):
            self.__effects.append(del_effect)
            return common_variables_ids

        return set()

    def find_args(self):
        args = set().union(*[self._find_args_in_literal(condition)
                             for condition in self.__conditions])
        args = args.union(*[self._find_args_in_literal(effect)
                            for effect in self.__effects])
        return args

    @property
    def effects(self):
        return self.__effects.copy()

    def is_threatened_by(self, transition: 'Transition') -> bool:
        for effect in transition.effects:
            for condition in self.__conditions:
                if self._are_possibly_the_same(effect, condition):
                    return True
            # Delete effect should not be after the add effect.
            # It somehow might be confusing because the interpretation
            # is like our negative effect is threatened by another
            # positive effect, so the positive effect should be placed
            # after the negative one.
            if not effect.negated:
                for effect2 in self.__effects:
                    if effect2.negated:
                        if self._are_possibly_the_same(effect, effect2):
                            return True
        return False

    def to_string(self, indent) -> str:
        output = ""
        if not self.__conditions:
            for effect in self.__effects:
                output += f"{indent}{literal_to_string(effect)}\n"
            return output

        def literals_to_string(indent, literals):
            if not literals:
                return indent + "(and)\n"
            if len(literals) == 1:
                return indent + literal_to_string(literals[0]) + "\n"
            output  = indent + "(and "
            output += f"\n{indent}     ".join([literal_to_string(literal)
                                               for literal in literals])
            output += f"\n{indent})\n"
            return output

        output  = indent + "(when\n"
        output += literals_to_string(indent + "      ", self.__conditions)
        output += literals_to_string(indent + "      ", self.__effects)
        output += indent + ")\n"
        return output


class MicroAction:
    def __init__(self):
        self.__preconditions: List[Condition] = []
        self.__transitions: List[Transition] = []
        self.__args = set()

    @property
    def args(self):
        return self.__args.copy()

    @property
    def preconditions(self):
        return self.__preconditions.copy()  # deep copy?

    @property
    def transitions(self):
        return self.__transitions.copy() # deep copy?

    @property
    def effects(self):
        return [e for t in self.__transitions for e in t.effects]

    def add_precondition(self, condition: Condition):
        self.__preconditions.append(condition)
        self.__args.update(condition.find_args())
        return self

    def add_transition(self, transition: Transition):
        self.__transitions.append(transition)
        self.__args.update(transition.find_args())
        return self

    def is_threatened_by(self, other: 'MicroAction') -> bool:
        parts = self.__preconditions + self.__transitions
        return any(part.is_threatened_by(other_transition)
                   for other_transition in other.__transitions 
                   for part in parts)

    def merge(self, other: 'MicroAction') -> 'MicroAction':
        self.__preconditions.extend(other.__preconditions)
        self.__transitions.extend(other.__transitions)
        self.__args.update(other.__args)
        return self

    def to_string(self, action_name, args_types, indent) -> str:
        args = ' '.join([f"{arg} - {args_types[arg]}" for arg in self.__args])
        preconditions = f"{indent}\t\t(and\n"
        for precondition in self.__preconditions:
            preconditions += precondition.to_string(indent + "\t\t\t")
        preconditions += f"{indent}\t\t)\n"
        effects = f"{indent}\t\t(and\n"
        for transition in self.__transitions:
            effects += transition.to_string(indent + "\t\t\t")
        effects += f"{indent}\t\t)\n"

        output  = f"{indent}(:action {action_name}\n"
        output += f"{indent} :parameters ({args})\n"
        output += f"{indent} :precondition\n{preconditions}"
        output += f"{indent} :effect\n{effects}"
        output += f"{indent})"
        return output


class Knowledge:
    """Extracts and provide predicates' knowledge

    For some predicates, we can partition their arguments to the
    "counted variable" and the other "parameters". By, this
    partitioning, we can uniquely determine the value of the
    "counted variable" argument, when we are given the values for the
    other "parameters", in each possible state.

    Additionally, it finds state variable of the given problem, and
    determines each predicate belongs to which state variables.

    This class extracts and provides these kinds of knowledge.
    """

    def __init__(self, task: Task):
        self.__omitted_positions = dict()  # A dictionary from predicates to
                                           # the list of their `omitted_pos`s
                                           # (or, the positions of their
                                           # `counted variable`s).
        self.__variables = dict()  # predicate -> Set[variable-id],
                                   # it shows each predicate participate
                                   # in which state variables.
        self.__extract_knowledge(task)

    def get_relations(self, predicate: Predicate) -> List[Tuple[str, str]]:
        relations = []
        for omitted_position in self.__omitted_positions.get(predicate[0], []):
            counted_variable = predicate[1][omitted_position]
            for arg in predicate[1]:
                if arg == counted_variable:
                    continue
                relations.append((arg, counted_variable))
        return relations

    def get_variables(self, literal: Literal):
        return self.__variables.get(literal.predicate, set()).copy()

    def __extract_knowledge(self, task: Task):
        normalize.normalize(task)
        invariants = find_invariants(task, None)
        invariant_size = self.__exactly_one_invariants(invariants, task.init)
        for invariant in invariant_size:
            for part in invariant.parts:
                if part.omitted_pos != -1:
                    (self
                     .__omitted_positions
                     .setdefault(part.predicate, [])
                     .append(part.omitted_pos))

        state_variables = self.__find_state_variables(invariant_size)
        for variable_id, invariant in enumerate(state_variables):
            for predicate in invariant.predicates:
                self.__variables.setdefault(predicate, set()).add(variable_id)

    @staticmethod
    def __exactly_one_invariants(invariants, initial_state):
        """Finds invariants with weight one and returns their sizes

        First filters out every invariants with weight not equal to one,
        and then returns the sizes of the remaining invariants (the
        number of all possible indices, in our "array" analogy).

        Returns:
            Dict[Invariant, int]: Maps Invariants to their sizes
        """

        # NOTE: The following code is similar to the `useful_groups()`
        #       function, but with slight modifications, to keep the
        #       invariants lifted, and also returns the number of
        #       possible groups(grounded versions) of each invariants.
        predicate_to_invariants = dict()
        for invariant in invariants:
            for predicate in invariant.predicates:
                (predicate_to_invariants
                 .setdefault(predicate, [])
                 .append(invariant))

        nonempty_groups = set()
        overcrowded_groups = set()
        for atom in initial_state:
            if isinstance(atom, pddl.Assign):
                continue
            for invariant in predicate_to_invariants.get(atom.predicate, []):
                group_key = (invariant, tuple(invariant.get_parameters(atom)))
                if group_key not in nonempty_groups:
                    nonempty_groups.add(group_key)
                else:
                    overcrowded_groups.add(group_key)
        useful_groups = nonempty_groups - overcrowded_groups
        invariant_size = dict()
        for (invariant, _) in useful_groups:
            invariant_size[invariant] = invariant_size.get(invariant, 0) + 1
        return invariant_size

    @staticmethod
    def __find_state_variables(invariant_size: Dict[Invariant, int]):
        memoized_value = {frozenset(): ([], 0)}  # predicates -> best value
        def __find_minimum_state_variables(predicates):
            # NOTE: Finding minimum state variable is done by using
            #       exhaustive search with memoization technique. I
            #       believe the number of possible state variables isn't
            #       too much; if my assumption is not correct, then our
            #       memory consumption and runtime will be overwhelming.
            predicates = frozenset(predicates)
            if predicates in memoized_value:
                return memoized_value[predicates]
            memoized_value[predicates] = ([], float('inf'))
            (selected_state_variables, minimum_number) = ([], float('inf'))
            for invariant in invariant_size:
                if predicates.isdisjoint(invariant.predicates):
                    continue
                remaining_predicates = predicates - invariant.predicates
                (state_variables, number) =\
                    __find_minimum_state_variables(remaining_predicates)
                number += invariant_size[invariant]
                if number < minimum_number:
                    minimum_number = number
                    selected_state_variables = state_variables + [invariant]
            result = (selected_state_variables, minimum_number)
            memoized_value[predicates] = result
            return result

        predicates = set()
        for invariant in invariant_size:
            for predicate in invariant.predicates:
                predicates.add(predicate)

        (state_variables, _) = __find_minimum_state_variables(predicates)
        return state_variables


Vertex = TypeVar('Vertex')
class Graph(Generic[Vertex]):
    """Directed graph (representing the influential relation)

    Maintains the influential relation among variables. In other words,
    the graph has an edge (u, v) if and only if the variable u has an
    influence on
    variable v (or, variable v depends on variable u).

    Additionally, this class produces a topological order of the
    vertices.
    """
    def __init__(self, vertices: List[Vertex] = []):
        self.__graph = {vertex: [] for vertex in vertices}

    def __str__(self) -> str:
        return str(self.__graph)

    @property
    def vertices(self):
        return [*self.__graph]

    def add_edge(self, edge: Tuple[Vertex, Vertex]):
        source, destination = edge
        self.__graph.setdefault(source, []).append(destination)
        return self

    def topological_order(self, vertex_priority=None) -> List[Vertex]:
        def dfs(vertex, visited, order):
            visited.append(vertex)
            neighbors = self.__graph[vertex]
            if vertex_priority:
                neighbors.sort(key=vertex_priority)
            for neighbor in neighbors:
                if neighbor in visited:
                    continue
                visited, order = dfs(neighbor, visited, order)
            return visited, [vertex] + order

        order = []
        visited = []
        for vertex in self.__graph:
            if vertex not in order:
                visited, order = dfs(vertex, visited, order)

        return order


class Action:
    """Represents an `Action` by a chain of micro-actions

    Decomposes an action into a series of micro-actions, then
    Order them in a way to help the searching process."""

    START_PROCEDURE = "start_procedure"
    STEP_TYPE = "steps"

    def __init__(self,
                 knowledge: Knowledge,
                 action: pddl.Action,
                 max_arguments: int,
                 default_values: Dict[str, str]):  # type to default value
        self.__knowledge = knowledge
        self.__new_objects = []
        self.__new_predicates = []
        self.__name = action.name
        self.__args = {p.name: p.type_name for p in action.parameters}
        self.__micro_actions = self.__split_action(action, max_arguments)
        self.__chain_micro_actions(default_values)

    @property
    def new_objects(self):
        return self.__new_objects.copy()

    @property
    def new_predicates(self):
        return self.__new_predicates.copy()

    @property
    def name(self):
        return self.__name

    def to_string(self, indent: str) -> str:
        return "\n".join(m.to_string(f"{self.__name}_{i}", self.__args, indent)
                         for i, m in enumerate(self.__micro_actions))

    def __split_action(self, action, max_arguments) -> List[MicroAction]:
        conditions = get_conditions(action.precondition)
        parameters = [parameter.name for parameter in action.parameters]
        influential_order = self.__order_variables(parameters, conditions)
        conditions = self.__order_conditions(conditions, influential_order)
        conditions = [Condition(condition) for condition in conditions]
        conditions = [MicroAction().add_precondition(condition)
                      for condition in conditions]
        conditions = self.__merge_micro_actions(max_arguments, conditions)
        transitions = self.__get_transitions(action.effects)
        transitions = [reduce(lambda micro_action, transition:
                                micro_action.add_transition(transition),
                              cyclic_transitions,
                              MicroAction())
                       for cyclic_transitions in (self
                                                  .__find_cyclic_transitions
                                                  (transitions))]

        micro_actions = self.__order_micro_actions(conditions, transitions)
        micro_actions = self.__merge_micro_actions(max_arguments, 
                                                   micro_actions)
        return micro_actions

    def __get_transitions(self, raw_effects):
        effects = []
        for effect in raw_effects:
            if isinstance(effect, SimpleEffect):
                effects.append(([], effect.effect))
            elif isinstance(effect, ConditionalEffect):
                conditions = get_conditions(effect.condition)
                effects.append((conditions, effect.effect))
            elif isinstance(effect, Effect):
                conditions = get_conditions(effect.condition)
                effects.append((conditions, effect.literal))
            else:
                raise NotImplementedError("Unknown effect!")
        transitions = []
        del_effects = []
        for conditions, effect in effects:
            if isinstance(effect, Atom):
                variables = self.__knowledge.get_variables(effect)
                transitions.append(Transition(conditions, effect, variables))
            elif isinstance(effect, NegatedAtom):
                if not self.__knowledge.get_variables(effect):
                    transitions.append(Transition(conditions, effect, set()))
                else:
                    del_effects.append((conditions, effect))
            else:
                raise ValueError("Expected only literals as effect!")
        for conditions, effect in del_effects:
            variables = self.__knowledge.get_variables(effect)
            covered_variables = set()
            for transition in transitions:
                (covered_variables
                 .update(transition
                         .check_delete_effect(variables, conditions, effect)))
            if covered_variables != variables:
                print("WARNING: Not all variables are covered by:", effect)
                print("         We fix it by adding a (redundant) transition")
                transitions.append(Transition(conditions, effect, set()))
        return transitions

    def __order_variables(self, variables: List[str], conditions) -> List[str]:
        """Orders the vertices based on their influential relations"""

        # Filter out any condition except positive literals
        conditions = filter(lambda condition: isinstance(condition, Atom),
                            conditions)
        predicates = [(atom.predicate, atom.args) for atom in conditions]

        # Constructing the influential graph
        graph = Graph(variables)
        relations = list(chain(*[self.__knowledge.get_relations(predicate)
                                 for predicate in predicates]))
        graph = reduce(Graph.add_edge, relations, graph)

        return graph.topological_order()

    @staticmethod
    def __order_conditions(conditions: List[Literal], ordered_variables):
        appearance_rank = {variable: float('inf')
                           for variable in ordered_variables}
        influential_rank = {variable: i
                            for i, variable in enumerate(ordered_variables)}
        def get_ranking(condition):
            ranking = [(appearance_rank[arg], influential_rank[arg])
                       for arg in condition.args if arg.startswith("?")]
            ranking.sort()
            return ranking
        size = len(conditions)
        for i in range(size):
            best_ranking = get_ranking(conditions[i])
            for j in range(i + 1, size):
                ranking = get_ranking(conditions[j])
                if ranking < best_ranking:
                    best_ranking = ranking
                    conditions[i], conditions[j] = conditions[j], conditions[i]
            appearance_rank.update({arg: min(i, appearance_rank[arg])
                                    for arg in conditions[i].args
                                    if arg.startswith("?")})
        return conditions


    @staticmethod
    def __find_cyclic_transitions(transitions: List[Transition]):
        """Partitions the input into sets of cyclic transitions

        It is possible that a transition affect other transition's
        condition. This relation might even be cyclic. For example,
        one transition might affect the condition of another one, and
        the that one might affect the first one's condition.

        Returns:
            List[List[Transitions]]: Each element is a cyclic transitions list
        """

        # Constructing the ordered graph
        threats = {transition: [] for transition in transitions}
        for transition1, transition2 in permutations(transitions, 2):
            if transition1.is_threatened_by(transition2):
                threats[transition1].append(transition2)

        return get_sccs_adjacency_dict(threats)

    @staticmethod
    def __order_micro_actions(preconditions: List[MicroAction],
                              transitions: List[MicroAction]):
        graph = Graph(preconditions + transitions)
        # Adding preconditions' order
        graph = reduce(Graph.add_edge,
                       zip(preconditions, preconditions[1:]),
                       graph)
        
        # Postponing the modification of state variables until the point
        # we need their old values.
        graph = reduce(Graph.add_edge,
                       ((source, destination)
                        for source in graph.vertices
                        for destination in transitions
                        if source.is_threatened_by(destination)),
                       graph)

        # Performing the transitions after all their arguments have been fixed.
        first_variable_appearance = {}
        for index, precondition in enumerate(preconditions):
            for arg in precondition.args:
                if arg not in first_variable_appearance:
                    first_variable_appearance[arg] = index
        for transition in transitions:
            last_index = -1
            for arg in transition.args:
                index = first_variable_appearance.get(arg, -1)
                last_index = max(last_index, index)
            if last_index != -1:
                graph.add_edge((preconditions[last_index], transition))

        def priority(micro_action: MicroAction) -> List[int]:
            return (  [2] * len(micro_action.transitions)
                    + [1] * len(micro_action.preconditions))
        return graph.topological_order(vertex_priority=priority)

    @staticmethod
    def __merge_micro_actions(max_arguments:int,
                              micro_actions: List[MicroAction]):
        # TODO: We might be able to optimize this method to improve its result

        def should_be_merged(action1: MicroAction, action2: MicroAction):
            if len(action1.args) < len(action2.args):
                return should_be_merged(action2, action1)
            if action2.args and not action1.args.intersection(action2.args):
                return False
            return (action1.args.issuperset(action2.args)
                    or len(action1.args.union(action2.args)) <= max_arguments)

        processed = [micro_actions[0]]
        for micro_action in micro_actions[1:]:
            while processed and should_be_merged(processed[-1], micro_action):
                micro_action.merge(processed[-1])
                del processed[-1]
            processed.append(micro_action)
        return processed

    def __chain_micro_actions(self, default_values):
        assert self.__micro_actions,  "Expects one or more micro-actions"

        def use_predicate(predicate,
                          adder: MicroAction,
                          needing: List[MicroAction]):
            deleter = needing[-1]
            condition = Condition(Atom(*predicate))
            for micro_action in needing:
                micro_action.add_precondition(condition)
            if adder == deleter:
                return
            adder.add_transition(Transition([], Atom(*predicate), []))
            deleter.add_transition(Transition([], NegatedAtom(*predicate), []))

        use_predicate((self.START_PROCEDURE, ()),
                      self.__micro_actions[-1],
                      [self.__micro_actions[0]])

        procedure_name = f"{self.__name}_procedure"
        step = lambda s: f"step_{s}"
        self.__new_predicates.append((procedure_name,
                                      [TypedObject("?s", self.STEP_TYPE)],
                                      [step(0)]))
        for i in range(len(self.__micro_actions)):
            self.__new_objects.append(step(i))
            use_predicate((procedure_name, (step(i),)),
                            self.__micro_actions[i - 1],
                            [self.__micro_actions[i]])

        # Handling shared arguments
        shared_arguments = {arg: [] for arg in self.__args}
        argument_predicate = lambda argument: f"{self.__name}_{argument[1:]}"
        for micro_action in self.__micro_actions:
            for arg in micro_action.args:
                shared_arguments[arg].append(micro_action)
        for arg, shared_micro_actions in shared_arguments.items():
            if len(shared_micro_actions) < 2:
                continue
            arg_type = self.__args[arg]
            self.__new_predicates.append((argument_predicate(arg),
                                          [TypedObject(arg, arg_type)],
                                          [default_values[arg_type]]))
            use_predicate((argument_predicate(arg), (default_values[arg_type],)),
                          shared_micro_actions[-1],
                          [shared_micro_actions[0]])
            use_predicate((argument_predicate(arg), (arg,)),
                          shared_micro_actions[0], shared_micro_actions[1:])

        return self


def update_task(task: Task, actions: List[Action]) -> Task:
    STEP_TYPE = pddl.Type(Action.STEP_TYPE)
    def define_predicate(task: Task, predicate_info):
        predicate_name, args_types, initial_value = predicate_info
        task.predicates.append(pddl.Predicate(predicate_name, args_types))
        init = Atom(predicate_name, initial_value)
        task.init.append(init)
        task.goal = Conjunction((task.goal, init)).simplified()
        return task

    task.types.append(STEP_TYPE)
    task = define_predicate(task, (Action.START_PROCEDURE, (), ()))
    new_predicates = chain.from_iterable(action.new_predicates
                                         for action in actions)
    task = reduce(define_predicate, new_predicates, task)
    task.predicates = [p for p in task.predicates if p.name != "="]
    task.init = [l for l in task.init
                 if isinstance(l, Literal) and l.predicate != "="]
    new_objects = set().union(*[action.new_objects for action in actions])
    task.objects.extend([pddl.TypedObject(new_object, STEP_TYPE)
                         for new_object in new_objects])
    task.actions = actions
    return task


DOMAIN_TEMPLATE = """(define (domain {domain_name})
(:requirements {requirements})
(:types {types})
(:constants {constants})
(:predicates {predicates})
{actions}
)
"""

def domain_to_string(task: Task) -> str:
    types  = [f"{t.name} - {t.basetype_name}"
              for t in task.types if t.basetype_name]
    types += [t.name for t in task.types if not t.basetype_name]
    types  = " ".join(types)
    objects = {}
    for obj in task.objects:
        objects.setdefault(obj.type_name, []).append(obj.name)
    constants  = [f"{' '.join(objects[t])} - {t}" for t in objects if t]
    constants += [f"{' '.join(objects[t])}" for t in objects if not t]
    constants = "\n            ".join(constants)
    requirements = " ".join(task.requirements.requirements)
    def predicate_str(predicate):
        arguments = [f"{a.name} - {a.type_name}" if a.type_name else a.name
                     for a in predicate.arguments]
        return f"({' '.join([predicate.name, *arguments])})"
    predicates = "\n             ".join(predicate_str(p)
                                        for p in task.predicates)
    actions = "\n\n".join(action.to_string("") for action in task.actions)
    return DOMAIN_TEMPLATE.format(domain_name=task.domain_name,
                                  requirements=requirements,
                                  types=types,
                                  constants=constants,
                                  predicates=predicates,
                                  actions=actions)


def get_conditions(condition):
    if isinstance(condition, Conjunction):
        return list(chain(*[get_conditions(part)
                            for part in condition.parts]))
    if isinstance(condition, Literal):
        return [condition]
    if isinstance(condition, Truth):
        return []
    raise ValueError("Unexpected condition type!")


def literal_to_string(literal: Literal) -> str:
    predicate = f"({' '.join([literal.predicate, *literal.args])})"
    if literal.negated:
        return f"(not {predicate})"
    return predicate


PROBLEM_TEMPLATE = """(define (problem {problem_name})
(:domain {domain_name})
(:init {init})
(:goal {goal})
)
"""

def problem_to_string(task: Task):
    init = "\n       ".join(literal_to_string(l) for l in task.init)
    goals  = "(and "
    goals += "\n           ".join(literal_to_string(l)
                                  for l in get_conditions(task.goal))
    goals += ")"
    return PROBLEM_TEMPLATE.format(problem_name=task.task_name,
                                   domain_name=task.domain_name,
                                   init=init,
                                   goal=goals)


def output(domain: str, problem: str):
    domain_file = "splitted_domain.pddl"
    problem_file = "splitted_problem.pddl"
    with open(domain_file, "w") as output_file:
        output_file.write(domain)
    with open(problem_file, "w") as output_file:
        output_file.write(problem)


def find_default_objects(task: Task):
    parents = {t.name: t.basetype_name for t in task.types}
    defaults = {}
    for obj in task.objects:
        type_name = obj.type_name
        while type_name:
            defaults.setdefault(type_name, obj.name)
            type_name = parents.get(type_name, None)
    return defaults


def filter_not_instantiable_actions(defaults, task: Task) -> Task:
    actions = []
    for action in task.actions:
        for parameter in action.parameters:
            if parameter.type_name not in defaults:
                break
        else:
            actions.append(action)
    task.actions = actions
    return task


if __name__ == "__main__":
    print("Parsing...")
    task = pddl_parser.open()
    print("Extract knowledge...")
    default_objects = find_default_objects(task)
    task = filter_not_instantiable_actions(default_objects, task)
    normalize.normalize(task)
    knowledge = Knowledge(task)
    print("Splitting actions ...")
    actions = [Action(knowledge, action, MAX_ARGUMENTS, default_objects)
               for action in task.actions]
    task = update_task(task, actions)
    domain_str = domain_to_string(task)
    problem_str = problem_to_string(task)
    output(domain_str, problem_str)