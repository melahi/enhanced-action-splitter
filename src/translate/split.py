#! /usr/bin/env python3


import pddl_parser
from splitting import main


if __name__ == "__main__":
    print("Parsing...")
    task = pddl_parser.open()
    main(task)