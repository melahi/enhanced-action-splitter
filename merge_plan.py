#! /usr/bin/env pypy3

import argparse
import sys


def get_args():
    parser = argparse.ArgumentParser(description="Merge plan which is generated for a split instance, to solve the original problem.")
    parser.add_argument("domain", help="PDDL domain file path")
    parser.add_argument("problem", help="PDDL problem file path")
    parser.add_argument("split_domain", help="The path for the split version of PDDL domain")
    parser.add_argument("split_problem", help="The path for the split version of PDDL problem")
    parser.add_argument("input_plan", help = "Input plan path, generated for the split version")
    parser.add_argument('-o', '--output_plan',
                        help="Output file to write the plan for the original problem instance (default: './plan')",
                        nargs='?',
                        default='./plan')
    args = parser.parse_args()
    return args.domain, args.problem, args.split_domain, args.split_problem, args.input_plan, args.output_plan


if __name__ == "__main__":
    parameters = get_args()
    sys.path.append('src/')
    from splitting import merge_plan
    print("Output:", parameters[-1])
    merge_plan(*parameters)
