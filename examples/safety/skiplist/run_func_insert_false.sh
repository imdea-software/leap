#!/bin/sh

#Configure path to Leap
LEAP=leap

OPTIONS="-q -co union -sm -yices+z3 -dp tsl"

PRG=prgs/func_insert.prg
INV_FOLDER=invs/func_insert
GRAPH=graphs/func_insert_false.graph
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

