LEAP=../../../leap
#OPTIONS="-l logFile --show_file_info -smt -sm -yices+z3 -dp tll -co union -do benchmarks/fullorder"
#OPTIONS="--show_file_info -smt -sm -yices+z3 -dp tll -co union -do benchmarks/fullorder"
#OPTIONS="-l logFile --show_file_info --show_file_info -smt -sm -yices+z3 -dp tll -co pruning"
OPTIONS="-smt -sm -yices+z3 -dp tll -co pruning"

PRG=prgs/list.prg
INV_FOLDER=invs
GRAPH=graphs/list.graph
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

