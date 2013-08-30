LEAP=../../../leap

#OPTIONS="-l logFile -co union -sm -sat -yices+z3 -dp tsl -do benchmarks --show_file_info"
OPTIONS="--focus $1 --show_file_info -co union -sm -sat -yices+z3 -dp tsl"

PRG=prgs/skiplist.prg
INV_FOLDER=invs
GRAPH=graphs/skiplist.graph
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

