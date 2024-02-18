from typing import Iterable, List, Set, Dict
from itertools import combinations, permutations, product
from functools import reduce

from sccs import get_sccs_adjacency_dict
import pddl
from pddl import SimpleEffect, ConditionalEffect, Effect, Atom, NegatedAtom
from pddl import Literal, TypedObject

from .common import get_conditions
from .knowledge import Knowledge
from .micro_action import Condition, Transition, MicroAction
from .node import Node
from .areces_node import ArecesNode
from .random_walk import random_walk
from .beam_search import beam_search


# BEAM_SEARCH_WIDTH = 400
# print("BEAM_SEARCH_WIDTH:", BEAM_SEARCH_WIDTH)
# DECISION_THRESHOLD = 2
# print("DECISION THRESHOLD:", DECISION_THRESHOLD)


class Action:
    """Represents an `Action` by a chain of micro-actions

    Decomposes an action into a series of micro-actions, then
    Order them in a way to help the searching process."""

    START_PROCEDURE = "start_procedure"
    STEP_TYPE = "splitting_step_type"

    def __init__(self,
                 knowledge: Knowledge,
                 action: pddl.Action,
                 size_threshold: int,
                 random_walk_timeout: int):
        self.__knowledge = knowledge
        self.__new_objects = []
        self.__new_predicates = []
        self.__name = action.name
        self.__args = action.parameters
        self.__random_walk_timeout = random_walk_timeout
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

    def _set_micro_actions(self, micro_actions: List[MicroAction]):
        self.__micro_actions = micro_actions.copy()
        return self

    def _set_name(self, name):
        self.__name = name
        return self

    def _set_args(self, args):
        self.__args = args
        return self

    def __split_action(self, action, size_threshold) -> List[MicroAction]:
        preconditions = [MicroAction().add_precondition(Condition(c))
                         for c in get_conditions(action.precondition)]
        transitions = self.__get_transitions(action.effects)
        transitions = self.__prepare_transitions(transitions)
        # micro_actions = self.__order_micro_actions_areces(preconditions,
        #                                                   transitions,
        #                                                   size_threshold)
        micro_actions = self.__order_micro_actions(preconditions,
                                                   transitions,
                                                   size_threshold)
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
            # variables = self.__knowledge.get_variables(effect)
            # covered_variables = set()
            # for transition in transitions:
            #     (covered_variables
            #      .update(transition
            #              .check_delete_effect(variables, conditions, effect)))
            # if covered_variables != variables:
            #     # Not all variables are covered by the current transitions;
            #     # it might be the case when we have state variables that just
            #     # falsify their values. Other probability might be that the
            #     # logical consequence implementation might not be precise.
            #     # In any case we fix it by adding a (probably redundant)
            #     # transition.
                transitions.append(Transition(conditions, effect, set()))
        return transitions

    def __prepare_transitions(self,
                              transitions: List[Transition]
                             ) -> List[MicroAction]:
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
            if transition1.is_threatened_by(transition2,
                                            self.__distinct_args):
                graph[transition1].append(transition2)

        components = get_sccs_adjacency_dict(graph)

        transitions = [reduce(lambda micro_action, transition:
                                 micro_action.add_transition(transition),
                              component,
                              MicroAction())
                       for component in components]
        return transitions

    def __order_micro_actions(self,
                              preconditions: List[MicroAction],
                              transitions: List[MicroAction],
                              size_threshold: int):
        print("Action:", self.__name)
        Node.prepare_class_variables(preconditions=preconditions,
                                     transitions=transitions,
                                     size_threshold=size_threshold,
                                     knowledge=self.__knowledge,
                                     action_args=self.__args,
                                     distinct_args=self.__distinct_args)
        initial = Node([MicroAction()], preconditions, transitions, 0)
        best = random_walk(initial, self.__random_walk_timeout)
        print(self.__name, "best node cost:", best.cost)
        chained_micro_actions = best.ordered_micro_actions()
        return chained_micro_actions
        conditions = set().union(*[p.preconditions for p in preconditions])
        return self.__complete_micro_actions(chained_micro_actions, conditions)

    def __order_micro_actions_areces(self,
                                     preconditions: List[MicroAction],
                                     transitions: List[MicroAction],
                                     size_threshold: int):
        print("Action:", self.__name)
        Node.knowledge = self.__knowledge
        graph = Node.create_dependency_graph(preconditions,
                                             transitions,
                                             self.__distinct_args)
        max_split_size = len(preconditions) + len(transitions)
        max_interface_size = len(set().union(*[m.args for m in graph.vertices]))
        ArecesNode.prepare_class_variables(max_split_size,
                                           max_interface_size,
                                           is_areces_cost=False,
                                           knowledge=self.__knowledge,
                                           action_args=self.__args,
                                           preconditions=preconditions,
                                           ground_size_threshold=size_threshold)
        initial = ArecesNode(graph, 0)
        best = beam_search(initial, 1, self.__random_walk_timeout)
        print(self.__name, "best node cost:", best.cost)
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
        2. positive conditions with the arguments which are the
           subset of the transition's arguments.
        """
        def complete(conditions: Set[Condition], micro_action: MicroAction):
            # Throw away negative conditions
            conditions = filter(lambda c: not c.condition.negated, conditions)
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
        distinct_args: Dict[str, Set[str]] = dict()
        def get_name(arg):
            return arg.name if isinstance(arg, TypedObject) else arg
        for precondition in preconditions:
            if not isinstance(precondition, NegatedAtom):
                continue
            if precondition.predicate != "=":
                continue
            name1 = get_name(precondition.args[0])
            name2 = get_name(precondition.args[1])
            distinct_args.setdefault(name1, set()).add(name2)
            distinct_args.setdefault(name2, set()).add(name1)

        for arg1, arg2 in combinations(self.__args, 2):
            type1, type2 = (arg1.type_name, arg2.type_name)
            if not self.__knowledge.has_shared_elements(type1, type2):
                distinct_args.setdefault(arg1.name, set()).add(arg2.name)
                distinct_args.setdefault(arg2.name, set()).add(arg1.name)
        return distinct_args
