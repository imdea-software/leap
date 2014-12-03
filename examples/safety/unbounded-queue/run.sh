#!/bin/sh

#Configure path to Leap
LEAP=leap

OPTIONS="-v 1 -sm -yices+z3 -dp tll -co pruning"

PRG=prgs/queue.prg
INV_FOLDER=invs/gral
GRAPH=graphs/queue.graph
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

