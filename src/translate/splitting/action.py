from typing import Iterable, List, Set
from itertools import combinations, permutations
from functools import reduce

from sccs import get_sccs_adjacency_dict
import pddl
from pddl import SimpleEffect, ConditionalEffect, Effect, Atom, NegatedAtom
from pddl import Literal, TypedObject

from .common import get_conditions
from .knowledge import Knowledge
from .micro_action import Condition, Transition, MicroAction
from .graph import Graph
from .abstract_node import AbstractNode
from .exhaustive_search import exhaustive_search


BEAM_SEARCH_WIDTH = 400
print("BEAM_SEARCH_WIDTH:", BEAM_SEARCH_WIDTH)
DECISION_THRESHOLD = 2
print("DECISION THRESHOLD:", DECISION_THRESHOLD)


class Action:
    """Represents an `Action` by a chain of micro-actions

    Decomposes an action into a series of micro-actions, then
    Order them in a way to help the searching process."""

    START_PROCEDURE = "start_procedure"
    STEP_TYPE = "steps"

    def __init__(self,
                 knowledge: Knowledge,
                 action: pddl.Action,
                 size_threshold: int):
        self.__knowledge = knowledge
        self.__new_objects = []
        self.__new_predicates = []
        self.__name = action.name
        self.__args = action.parameters
        preconditions = get_conditions(action.precondition)
        self.__distinct_args = self.__find_distinct_args(preconditions)
        self.__micro_actions = self.__split_action(action, size_threshold)
        self.__chain_micro_actions(knowledge.default_objects)

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
        if len(self.__micro_actions) == 1:
            return self.__micro_actions[0].to_string(self.__name,
                                                     self.__args,
                                                     indent)
        return "\n".join(m.to_string(f"{self.__name}_{i}", self.__args, indent)
                         for i, m in enumerate(self.__micro_actions))

    def __split_action(self, action, size_threshold) -> List[MicroAction]:
        preconditions = {Condition(c)
                         for c in get_conditions(action.precondition)}
        transitions = self.__get_transitions(action.effects)
        transitions = self.__prepare_transitions(transitions)
        # micro_actions = preconditions + transitions
        micro_actions = self.__order_micro_actions(preconditions,
                                                   transitions,
                                                   size_threshold)
        micro_actions = self.__complete_micro_actions(micro_actions,
                                                      preconditions)
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
                # Not all variables are covered by the current transitions;
                # it might be the case when we have state variables that just
                # falsify their values. Other probability might be that the
                # logical consequence implementation might not be precise.
                # In any case we fix it by adding a (probably redundant)
                # transition.
                transitions.append(Transition(conditions, effect, set()))
        return transitions

    def __prepare_transitions(self,
                              transitions: List[Transition]) -> List[MicroAction]:
        """Prepares the transitions

        It is important to consider the possibility that a transition
        affect other transition's condition. This relation might be
        cyclic. For example, one transition might affect the condition
        of another one, and that one might affect the first one's
        condition. Here, we find those transitions and merge them.

        Returns:
            List[MicroAction]: List of transitions
        """
        # Constructing the ordered graph
        graph = {transition: [] for transition in transitions}
        for transition1, transition2 in permutations(transitions, 2):
            if transition1.is_threatened_by(transition2, self.__distinct_args):
                graph[transition1].append(transition2)

        components = get_sccs_adjacency_dict(graph)

        transitions = [reduce(lambda micro_action, transition:
                                 micro_action.add_transition(transition),
                              component,
                              MicroAction())
                       for component in components]
        return transitions

    def __order_micro_actions(self,
                              preconditions: List[Condition],
                              transitions: List[MicroAction],
                              size_threshold: int):

        def get_args(literal: Literal):
            return [a.name if isinstance(a, TypedObject) else a
                    for a in literal.args]
        def is_variable(argument: str):
            return argument.startswith("?")
        def get_omittable_variables(condition: Condition):
            literal = condition.condition
            predicate = (literal.predicate, get_args(literal))
            return [a
                    for a in self.__knowledge.omittable_arguments(predicate)
                    if is_variable(a)]

        memoized_estimate = {}
        def count_estimate(micro_action: MicroAction) -> int:
            key = (frozenset(micro_action.args),
                   tuple(micro_action.preconditions))
            if key not in memoized_estimate:
                memoized_estimate[key] = self.__count_estimate(key[0], key[1])
            return memoized_estimate[key]

        statics = [p
                   for p in preconditions
                   if self.__knowledge.is_static(p.condition.predicate)]

        # Check earlier transitions have no threatening relations with
        # later ones.
        distinct_args = self.__distinct_args
        for transition1 in transitions:
            for transition2 in transitions:
                if transition1 == transition2:
                    break
                assert not transition1.is_threatened_by(transition2,
                                                        distinct_args),\
                       "We assume that earlier transitions do not threats "\
                       "later ones!"

        class Candidate(AbstractNode):
            def __init__(self,
                         micro_actions: List[MicroAction],
                         preconditions: List[Condition],
                         transitions: List[MicroAction]):
                # NOTE: `micro_actions[:-1]` are fixed; we can/should only
                #        modify the `micro_actions[-1]`.
                self.__micro_actions = micro_actions  #chained micro-actions
                self.__preconditions = preconditions  # remaining preconditions
                self.__transitions = transitions  # remaining transitions
                self.__key = tuple((frozenset(m.preconditions),
                                    frozenset(m.transitions))
                                   for m in micro_actions)
                self.__cost = None

            def __hash__(self) -> int:
                return hash(self.__key)

            def __eq__(self, __o: 'Candidate') -> bool:
                return self.__key == __o.__key

            def __lt__(self, __o: 'Candidate') -> bool:
                return self.__calculate_cost() < __o.__calculate_cost()

            def ordered_micro_actions(self):
                assert not self.__preconditions and not self.__transitions,\
                       "Expected not having remaining precondition or "\
                       "transition"
                return self.__micro_actions.copy()

            def neighbors(self) -> List['Candidate']:
                if not self.__preconditions and not self.__transitions:
                    # It is a terminal node
                    return []

                candidates = []
                dependency_graph = self.__construct_dependency_graph()
                last = self.__micro_actions[-1]
                for precondition in self.__preconditions:
                    if (    last.args
                        and last.args.isdisjoint(precondition.find_args())):
                        continue
                    if dependency_graph.neighbors(precondition):
                        # `precondition` has some dependencies
                        continue
                    new_micro_action = last.copy()
                    new_micro_action.add_precondition(precondition)
                    estimate = count_estimate(new_micro_action)
                    if estimate > size_threshold:
                        continue
                    candidates.append(self.__get_child(new_micro_action,
                                                       estimate))
                if candidates:
                    return candidates

                if last.args:
                    return [Candidate(self.__micro_actions + [MicroAction()],
                                      self.__preconditions,
                                      self.__transitions)]
                assert not self.__preconditions,  "No precondition expected"
                new_micro_action = last.copy()
                new_micro_action.merge(self.__transitions.pop(0))
                estimate = count_estimate(new_micro_action)
                return [self.__get_child(new_micro_action, estimate)]

            def __construct_dependency_graph(self):
                determined = set().union(*[m.args for m in self.__micro_actions])
                def is_helping(subject: Condition, object: Condition):
                    if not isinstance(subject, Atom):
                        return False
                    determinable_vars = get_omittable_variables(subject)
                    determinable_vars = set(determinable_vars) - determined
                    clueless_vars = object.find_args() - determined
                    if isinstance(object, Atom):
                        clueless_vars -= get_omittable_variables(object)

                    # At most one variable of the `determinable_vars` can
                    # be determined
                    return (    determinable_vars
                            and clueless_vars.issuperset(determinable_vars))

                graph = Graph(self.__preconditions)
                graph = reduce(Graph.add_edge,
                               filter(lambda edge: is_helping(*edge),
                                      permutations(self.__preconditions, r=2)),
                               graph)
                graph.make_acyclic()
                return graph

            def __calculate_cost(self):
                # Cost criteria:
                # 1. spans of preconditional components,
                #       preconditional component:
                #          The set of micro-actions with preconditions that 
                #          are connected in the term of their sharing arguments
                # 2. number of micro-actions with preconditions,
                # 3. total number of micro-actions,
                # 4. the sum of the estimate count of grounded micro-actions.
                # TODO: Perhaps we could also consider the number of
                #       decisions (args count - useful omittable args) that
                #       we need to make, in our cost criteria
                # TODO: It is also interesting to measure the importance of
                #       each criterion.

                if self.__cost is not None:
                    return self.__cost

                assert not self.__preconditions and not self.__transitions,\
                       "cost is not defined for uncompleted candidates"

                # Finding components
                components = []
                for micro_action in self.__micro_actions:
                    if not micro_action.has_precondition:
                        continue
                    old_components = []
                    new_component = micro_action.args
                    for component in components:
                        if new_component.isdisjoint(component):
                            old_components.append(component)
                        else:
                            new_component.update(component)
                    components = old_components + [new_component]

                spans = []
                for component in components:
                    first = len(self.__micro_actions)
                    last = 0
                    for i, micro_action in enumerate(self.__micro_actions):
                        if (   not micro_action.has_precondition
                            or micro_action.args.isdisjoint(component)):
                            continue
                        first = min(first, i)
                        last = max(last, i)
                    spans.append(last - first + 1)
                spans.sort(reverse=True)

                preconditions_count = 0
                ground_estimate = 0
                for micro_action in self.__micro_actions:
                    ground_estimate += count_estimate(micro_action)
                    if micro_action.has_precondition:
                        preconditions_count += 1

                self.__cost = (spans,
                               preconditions_count,
                               len(self.__micro_actions),
                               ground_estimate)
                return self.__cost

            def __get_child(self,
                            new_micro_action: MicroAction,
                            size_threshold: int) -> 'Candidate':
                # Adding static precondition as much as possible
                level_off = False
                while not level_off:
                    level_off = True
                    for static_condition in statics:
                        if static_condition in new_micro_action.preconditions:
                            continue
                        temp = new_micro_action.copy()
                        temp.add_precondition(static_condition)
                        if count_estimate(temp) <= size_threshold:
                            new_micro_action = temp
                            # Imposing a new condition/constraint might limit
                            # the possibilities so we can add some other
                            # static conditions. Therefore, we set `level_off`
                            # to `False`.
                            level_off = False

                # Include all preconditions having a subset of arguments
                remaining_preconditions: List[Condition] = []
                for precondition in self.__preconditions:
                    if new_micro_action.args.issuperset(precondition.find_args()):
                        # This addition might be redundant; `precondition`
                        # might already exist in the `new_micro_action`.
                        new_micro_action.add_precondition(precondition)
                    else:
                        remaining_preconditions.append(precondition)

                # Include all transitions having a subset of arguments which
                # threat no remaining precondition or transition!
                remaining_transitions: List[MicroAction] = []
                def is_it_safe_to_include(transition: MicroAction):
                    if not new_micro_action.args.issuperset(transition.args):
                        return False
                    for precondition in remaining_preconditions:
                        if any(precondition.is_threatened_by(t,distinct_args)
                               for t in transition.transitions):
                           return False
                    if any(t.is_threatened_by(transition, distinct_args)
                           for t in remaining_transitions):
                        return False
                    return True
                for transition in self.__transitions:
                    if is_it_safe_to_include(transition):
                        new_micro_action.merge(transition)
                    else:
                        remaining_transitions.append(transition)

                micro_actions = self.__micro_actions[:-1] + [new_micro_action]
                return Candidate(micro_actions,
                                 remaining_preconditions,
                                 remaining_transitions)

        initial = Candidate([MicroAction()], preconditions, transitions)
        best = exhaustive_search(initial)
        return best.ordered_micro_actions()

    def __complete_micro_actions(self,
                                 micro_actions: List[MicroAction],
                                 partial_state: Set[Condition]):
        """Add related conditions to each micro-action

        Find micro-action's related conditions and add them -as much as
        possible- to it. Related conditions are:

        1. static conditions overlapped with transition's
           arguments which doesn't increase the number of its
           ground instances, 
        2. conditions with the arguments which are the subset
           of the transition's arguments.
        """
        def complete(conditions: Set[Condition], micro_action: MicroAction):
            # Sort conditions to make our method deterministic (reproducible)
            conditions = sorted(conditions, key=lambda c: c.to_string(""))
            level_off = False
            current_size = self.__count_estimate(micro_action.args,
                                                 micro_action.preconditions)
            while not level_off:
                level_off = True
                best = (-1, None)
                for condition in conditions:
                    args = condition.find_args()
                    if micro_action.args.isdisjoint(args):
                        continue
                    new_args = micro_action.args | args
                    new_conditions = (  set(micro_action.preconditions)
                                      | {condition})
                    new_size = self.__count_estimate(new_args, new_conditions)
                    if new_size <= current_size and new_size > best[0]:
                        best = (new_size, condition)
                if best[1] is not None:
                    micro_action.add_precondition(best[1])
                    conditions.remove(best[1])
                    level_off = False
                    current_size = best[0]
            return micro_action

        for micro_action in micro_actions:
            complete(partial_state, micro_action)
            partial_state = (micro_action
                             .update_partial_state(partial_state,
                                                   self.__distinct_args))
        return micro_actions

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
        shared_arguments = {arg.name: [] for arg in self.__args}
        argument_predicate = lambda argument: f"{self.__name}_{argument[1:]}"
        for micro_action in self.__micro_actions:
            for arg in micro_action.args:
                shared_arguments[arg].append(micro_action)
        for arg_name, shared_micro_actions in shared_arguments.items():
            if len(shared_micro_actions) < 2:
                continue
            arg = next(a for a in self.__args if a.name == arg_name)
            self.__new_predicates.append((argument_predicate(arg.name),
                                          [arg],
                                          [default_values[arg.type_name]]))
            use_predicate((argument_predicate(arg.name),
                           (default_values[arg.type_name],)),
                          shared_micro_actions[-1],
                          [shared_micro_actions[0]])
            use_predicate((argument_predicate(arg.name), (arg.name,)),
                          shared_micro_actions[0], shared_micro_actions[1:])

        return self

    def __count_estimate(self, args, conditions: Iterable[Condition]):
        args = [a for a in self.__args if a.name in args]
        conditions = [c.condition for c in conditions]
        return self.__knowledge.all_count_estimate(args, conditions)

    def __find_distinct_args(self, preconditions: List[Literal]):
        distinct_args = {}
        def get_name(arg):
            return arg.name if isinstance(arg, TypedObject) else arg
        for precondition in preconditions:
            if not isinstance(precondition, NegatedAtom):
                continue
            if precondition.predicate != "=":
                continue
            name1 = get_name(precondition.args[0])
            name2 = get_name(precondition.args[1])
            distinct_args.setdefault(name1, []).append(name2)
            distinct_args.setdefault(name2, []).append(name1)

        for arg1, arg2 in combinations(self.__args, 2):
            type1, type2 = (arg1.type_name, arg2.type_name)
            if not self.__knowledge.has_shared_elements(type1, type2):
                distinct_args.setdefault(arg1.name, []).append(arg2.name)
                distinct_args.setdefault(arg2.name, []).append(arg1.name)
        return distinct_args