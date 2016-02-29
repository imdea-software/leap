#!/bin/sh

#Configure path to Leap
LEAP=leap

OPTIONS="-focus $1 -v 1 -ovc -o vcs -smt -sm -yices+z3 -dp thm -co pruning"

PRG=prgs/hashmap.prg
INV_FOLDER=invs/gral
GRAPH=graphs/hashmap.graph
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

