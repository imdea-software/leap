#!/bin/sh

#Configure path to Leap
LEAP=leap

OPTIONS="-v 1 -ovc -o vcs -smt -sm -yices+z3 -dp tll -co pruning"

PRG=prgs/list.prg
INV_FOLDER=invs/gral
GRAPH=graphs/list.graph
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

