LEAP=../../leap
OPTIONS="--focus $1 --show_file_info -smt -sm -yices+z3 -dp tll -co union -do benchmarks/fullorder"

PRG=prgs/listorder.prg
INV_FOLDER=invs/fullorder_invs
GRAPH=graphs/test.graph
OUTPUT=out/test

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

