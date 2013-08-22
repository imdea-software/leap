LEAP=../../../leap

#OPTIONS="-l logFile -co union -sm -sat -yices+z3 -dp tsl -do benchmarks --show_file_info"
OPTIONS="--show_file_info --focus $1 -co union -sm -sat -yices+z3 -dp tslk[2]"

PRG=prgs/skiplist2.prg
INV_FOLDER=invs
GRAPH=graphs/skiplist2.graph
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

