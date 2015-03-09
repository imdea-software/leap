#!/bin/sh

#Configure path to Leap
LEAP=leap

OPTIONS="-co union -sm -yices+z3 -dp tslk[3]"

PRG=prgs/skiplist3.prg
INV_FOLDER=invs
GRAPH=graphs/skiplist3.graph
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

