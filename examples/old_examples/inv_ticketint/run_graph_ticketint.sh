LEAP=../../leap
OPTIONS="-fpm -sm -dp num -co pruning -hp -do benchmarks/ticketint"

PRG=prgs/ticketint.prg
INV_FOLDER=inv_cand
GRAPH=graphs/ticketint.graph
OUTPUT=out/ticketint_graph

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

