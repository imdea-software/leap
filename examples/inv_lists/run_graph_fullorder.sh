LEAP=../../leap
OPTIONS="--focus 34 --show_file_info -smt -sm -yices+z3 -dp tll -co union -do benchmarks/fullorder"

PRG=prgs/listorder.prg
INV_FOLDER=invs/fullorder_invs
GRAPH=graphs/fullorder.graph
OUTPUT=out/fullorder

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

