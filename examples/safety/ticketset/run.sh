#!/bin/sh

#Configure path to Leap
LEAP=leap

OPTIONS="-sm -dp num -co pruning"

PRG=prgs/ticketset.prg
INV_FOLDER=invs
GRAPH=graphs/ticketset.graph
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

