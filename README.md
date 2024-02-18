# Enhanced Action Splitter (EAS)

**EAS** is an open-source Python tool that efficiently splits PDDL action schemas into smaller actions suitable for grounding. This is particularly helpful when the number of grounded actions for action schemas becomes too large for grounding-based planners to handle, effectively enabling them to solve problems they otherwise couldn't.

Paper: [Optimizing the Optimization of Planning Domains by Automatic Action Schema
Splitting](https://users.aalto.fi/~rintanj1/jussi/papers/ElahiRintanen24aaai.pdf)


## Dependencies
```bash
pypy3 -m pip install -r requirements.txt
```
* `python3` also can be used instead of `pypy3`
* For `pypy3`, probably it is needed to install `apt install pypy3-dev` beforehand.

## Splitting:
The following command produces the split version of the problem instance in the `example` directory:
``` bash
pypy3 ./split.py example/domain.pddl example/problem.pddl example/split_domain.pddl example/split_problem.pddl
```

## Merging plan:
After solving the split instance, its plan (`split_plan`) can be merged to construct a solution for the original problem by the following command:
```bash
pypy3 ./merge_plan.py example/domain.pddl example/problem.pddl example/split_domain.pddl example/split_problem.pddl split_plan
```

## Notes
* This project leverages the well-known [Fast Downward](https://github.com/aibasel/downward) PDDL translator for efficient parsing and invariant synthesis capabilities.
* In our experiments, we used a slightly modified version of the [BFWS planner](https://github.com/ipc2023-classical/planner29.git). The patch file can be found in `BFWS_memory_enhancement_patch.zip`.
