LEAP=../../../leap

#OPTIONS="-l logFile -co union -sm -sat -yices+z3 -dp tsl -do benchmarks --show_file_info"
OPTIONS="-co union -sm -yices+z3 -dp tslk[1]"

PRG=prgs/skiplist1.prg
INV_FOLDER=invs
GRAPH=graphs/skiplist1.graph
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

