#!/bin/sh

#Configure path to Leap
LEAP=leap

OPTIONS="-q -sm -yices+z3 -dp tll -co pruning -v 1 -si -sf"

PRG=prgs/queue.prg
INV_FOLDER=invs/gral
GRAPH=graphs/queue.graph
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

