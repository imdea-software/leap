#!/bin/sh

#Configure path to Leap
LEAP=leap

OPTIONS="-smt -sm -yices+z3 -dp tll -co pruning"

PRG=prgs/list.prg
INV_FOLDER=invs/gral
AXIOMS_FOLDER=axioms
AXIOM_FILE=list.axioms
GRAPH=graphs/list.graph
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -af ${AXIOM_FILE} -a ${AXIOMS_FOLDER} -o ${OUTPUT}

