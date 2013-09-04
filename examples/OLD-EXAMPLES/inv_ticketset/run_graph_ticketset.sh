LEAP=../../leap
OPTIONS="-fpm -sm -dp num -co pruning -hp -do benchmarks/ticketset"

PRG=prgs/ticketset.prg
INV_FOLDER=inv_cand
GRAPH=graphs/ticketset.graph
OUTPUT=out/ticketset_graph

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

