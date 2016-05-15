#!/bin/sh

#Configure path to Leap
LEAP=leap

OPTIONS="-focus 22 -si -v 0 -yices+z3 -dp thm -co pruning -q"

PRG=prgs/hashtable.prg
INV_FOLDER=invs/gral
GRAPH=graphs/hashtable.graph
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

