#!/bin/sh

#Configure path to Leap
LEAP=leap

OPTIONS="-co union -sm -yices+z3 -dp tslk[2]"

PRG=prgs/skiplist2.prg
INV_FOLDER=invs
GRAPH=graphs/skiplist2.graph
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

