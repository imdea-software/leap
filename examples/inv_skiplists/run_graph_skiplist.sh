LEAP=../../leap
OPTIONS="-sm -yices+z3 -dp tsl -do benchmarks"

PRG=prgs/skiplist.prg
INV_FOLDER=invs/skiplist
GRAPH=graphs/skiplist.graph
OUTPUT=out/skiplist

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

