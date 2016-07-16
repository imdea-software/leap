#!/bin/sh

#Configure path to Leap
LEAP=leap

OPTIONS="-smt -sm -yices+z3 -dp tll -co pruning"

PRG=prgs/list_functional.prg
INV_FOLDER=invs/functional
GRAPH=graphs/list_functional_search_true.graph
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

