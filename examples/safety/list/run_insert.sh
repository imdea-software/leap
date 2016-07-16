#!/bin/sh

#Configure path to Leap
LEAP=leap

OPTIONS="-smt -sm -yices+z3 -dp tll -co pruning"

PRG=prgs/list_insert.prg
INV_FOLDER=invs/insert
GRAPH=graphs/list_insert.graph
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

