#!/bin/sh

#Configure path to Leap
LEAP=leap

OPTIONS="-si -sm -yices+z3 -dp tll -co pruning -focus $1 -v 1 -sf"

PRG=prgs/list.prg
INV_FOLDER=invs
GRAPH=graphs/list_extra.graph
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

