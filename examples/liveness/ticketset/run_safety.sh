#Configure path to Leap
LEAP=leap

OPTIONS="-v 1 -sm -dp pairs -co pruning -sf"

PRG=prgs/ticketset.prg
INV_FOLDER=invs
GRAPH=graphs/ticketset.graph
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

