LEAP=../../../leap

#OPTIONS="-l logFile -co union -sm -sat -yices+z3 -dp tsl -do benchmarks --show_file_info"
OPTIONS="--show_file_info --focus $1 -co union -sm -sat -yices+z3 -dp tsl"

PRG=prgs/skiplist.prg
INV_FOLDER=invs
GRAPH=graphs/skiplist.graph
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

