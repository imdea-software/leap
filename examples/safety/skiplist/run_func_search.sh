#!/bin/sh

#Configure path to Leap
LEAP=leap

OPTIONS="-q -co union -sm -yices+z3 -dp tsl"

PRG=prgs/func_search.prg
INV_FOLDER=invs/func_search
GRAPH=graphs/func_search.graph
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

