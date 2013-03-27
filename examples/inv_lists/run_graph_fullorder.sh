LEAP=../../leap
OPTIONS="-smt -sm -yices+z3 -dp tll -co union -do benchmarks/fullorder"

PRG=prgs/listorder.prg
INV_FOLDER=invs/fullorder_invs
GRAPH=graphs/fullorder.graph
OUTPUT=out/fullorder_graph

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

