#!/bin/sh

#Configure path to Leap
LEAP=leap

OPTIONS="-focus $1 -sm -si -v 1 -yices+z3 -dp thm -co pruning -q -testing"

PRG=prgs/hashtable.prg
INV_FOLDER=invs/gral
GRAPH=graphs/hashtable.graph
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

