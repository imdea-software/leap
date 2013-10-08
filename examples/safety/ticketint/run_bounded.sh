#Configure path to Leap
LEAP=leap

OPTIONS="--focus $1 -sm -dp num -co pruning"

PRG=prgs/ticketint_bounded.prg
INV_FOLDER=invs/bounded
GRAPH=graphs/ticketint_bounded.graph
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

