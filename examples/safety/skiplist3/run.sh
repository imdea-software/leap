LEAP=../../../leap

#OPTIONS="-l logFile -co union -sm -sat -yices+z3 -dp tsl -do benchmarks --show_file_info"
OPTIONS="--show_file_info -co union -sm -sat -yices+z3 -dp tslk[3]"

PRG=prgs/skiplist3.prg
INV_FOLDER=invs
GRAPH=graphs/skiplist3.graph
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

