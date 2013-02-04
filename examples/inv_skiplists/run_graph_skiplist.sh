LEAP=../../leap
OPTIONS="--focus 12 -fpm -sm -yices+z3 -dp tsl -co pruning -hp -do benchmarks --show_file_info"

PRG=prgs/skiplist.prg
INV_FOLDER=invs/skiplist
GRAPH=graphs/skiplist.graph
OUTPUT=out/skiplist

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

