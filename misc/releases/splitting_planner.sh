#! /usr/bin/bash

SPLITTED_DOMAIN_NAME="splitted_domain.pddl"
SPLITTED_PROBLEM_NAME="splitted_problem.pddl"
rm $SPLITTED_DOMAIN_NAME $SPLITTED_PROBLEM_NAME -f

domain_name=$1
problem_name=$2

~/3rd_party_planners/downward/src/translate/splitting.py $domain_name $problem_name
return_code=$?

if [[ $return_code -ne 0 ]]
then
	echo "Error: Could not split the task!"
	exit $return_code
fi

~/3rd_party_planners/downward/fast-downward.py --alias seq-sat-fdss-2018 --overall-time-limit 30m $SPLITTED_DOMAIN_NAME $SPLITTED_PROBLEM_NAME

# rm $SPLITTED_DOMAIN_NAME $SPLITTED_PROBLEM_NAME
