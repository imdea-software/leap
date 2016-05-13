#!/bin/sh

#Configure path to Leap
LEAP=leap

OPTIONS="-focus $1 -si -v 1 -sm -yices+z3 -dp thm -co pruning -q"

PRG=prgs/hashmap.prg
INV_FOLDER=invs/gral
GRAPH=graphs/hashmap.graph
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

