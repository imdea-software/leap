#!/bin/sh

#Configure path to Leap
LEAP=leap

OPTIONS="-v 1 -co union -sm -yices+z3 -dp tslk[5]"

PRG=prgs/skiplist5.prg
INV_FOLDER=invs
GRAPH=graphs/skiplist5.graph
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

