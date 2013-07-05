LEAP=../../leap_withpos.byte
#OPTIONS="-v -co union --focus $1 -sm -yices+z3 -dp tsl -do benchmarks --show_file_info"
OPTIONS="-v -co union --focus $1 -sm -yices+z3 -dp tsl --show_file_info"

PRG=prgs/skiplist.prg
INV_FOLDER=invs/skiplist
GRAPH=graphs/skiplist.graph
OUTPUT=out/skiplist

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

