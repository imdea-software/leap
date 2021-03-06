#!/bin/sh

#Configure path to Leap
LEAP=leap

OPTIONS="-q -co union -sm -yices+z3 -dp tsl"

PRG=prgs/func_remove.prg
INV_FOLDER=invs/func_remove
GRAPH=graphs/func_remove_false.graph
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

