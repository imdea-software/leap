LEAP=../../leap
#OPTIONS="-v -co union --focus $1 -sm -yices+z3 -dp tsl -do benchmarks --show_file_info"
#OPTIONS="-v -co union --focus $1 -sm -yices+z3 -dp tsl --show_file_info"
OPTIONS="--show_file_info -l logFile -co union -sm -sat -yices+z3 -dp tsl"
#OPTIONS="-l logFile -co union -sm -yices+z3 -dp tsl"

PRG=prgs/skiplist.prg
INV_FOLDER=invs/skiplist
GRAPH=graphs/skiplist.graph
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

