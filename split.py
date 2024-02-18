#! /usr/bin/env pypy3

import os
import sys
import argparse


def get_args():
    parser = argparse.ArgumentParser(description="Split PDDL domain and proble files.",
                                     formatter_class=argparse.RawTextHelpFormatter)
    parser.add_argument('domain', help="PDDL domain file path")
    parser.add_argument('problem', help="PDDL problem file path")
    parser.add_argument('split_domain',
                        help="The path to write the split domain (default: ./split_domain.pddl)",
                        default="./split_domain.pddl",
                        nargs="?")
    parser.add_argument('split_problem',
                        help="The path to write the split problem (default: ./split_problem.pddl)",
                        default="./split_problem.pddl",
                        nargs="?")
    parser.add_argument('--max-actions',
                        help="Maximum number of grounded actions (default: 1000000)",
                        type=int,
                        default=1_000_000)
    parser.add_argument('--max-time-per-action',
                        help="Maximum search time per actions in seconds (default: 50)",
                        type=int,
                        default=50)
    parser.add_argument('--max-search-time',
                        help="Maximum time for Monte Carlo Search in seconds (default: 500).\n"
                             "Note: This value can be overriden by --max-time-per-action * (number of actions).",
                        type=int,
                        default=500)
    args = parser.parse_args()
    return (args.max_actions,
            args.max_search_time,
            args.max_time_per_action,
            args.domain,
            args.problem,
            args.split_domain,
            args.split_problem)


if __name__ == "__main__":
    parameters = get_args()
    print("Parameters:", *parameters)
    src_dir = os.path.join(os.path.dirname(__file__), "src/")
    sys.path.append(src_dir)
    from splitting import split
    split(*parameters)
