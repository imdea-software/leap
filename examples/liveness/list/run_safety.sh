#!/bin/sh

#Configure path to Leap
LEAP=leap

OPTIONS="-sm -smt -yices+z3 -dp tll -co pruning -focus $1 -si -v 1"

PRG=prgs/list.prg
INV_FOLDER=invs
GRAPH=graphs/list.graph
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

