LEAP=../../../leap
OPTIONS="-sm -dp num -co pruning -do benchmarks/ticketint"

PRG=prgs/ticketint.prg
INV_FOLDER=invs
GRAPH=graphs/ticketint.graph
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

