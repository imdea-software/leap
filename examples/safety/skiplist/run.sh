#!/bin/sh

#Configure path to Leap
LEAP=leap

OPTIONS="-v 1 -q -co union -sm -yices+z3 -dp tsl"

PRG=prgs/skiplist.prg
INV_FOLDER=invs/gral
GRAPH=graphs/skiplist.graph
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

