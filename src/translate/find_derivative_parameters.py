#! /usr/bin/env python3

import os
import sys
import random
random.seed(14)

from splitting.find_derivatives import find_derivatives


def main():
    classical_domains_dir = "/home/sadra/classical-domains/classical/"
    sys.path.append(classical_domains_dir)
    for domain_name in os.listdir(classical_domains_dir):
        api = __import__(domain_name, globals(), locals(), ['api']).api
        if not api.domains:
            continue
        domain = api.domains[0]
        if not domain["problems"]:
            continue

        print("Domain:", domain_name)
        print()

        domain_path, problem_path = domain["problems"][-1]
        domain_path = os.path.join(classical_domains_dir, domain_path)
        problem_path = os.path.join(classical_domains_dir, problem_path)
        find_derivatives(domain_path, problem_path)
        print("--------------------------------------------------")


if __name__ == "__main__":
    main()