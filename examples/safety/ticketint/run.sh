#!/bin/sh

#Configure path to Leap
LEAP=leap

OPTIONS="-sm -dp num -co pruning"

PRG=prgs/ticketint.prg
INV_FOLDER=invs/gral
GRAPH=graphs/ticketint.graph
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

