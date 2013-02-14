LEAP=../../leap
OPTIONS="-v --focus 0 --show_file_info -yices+z3 -dp tll -sm -co union -do benchmarks/fullorder"

PRG=prgs/listorder.prg
INV_FOLDER=invs/fullorder_invs
GRAPH=graphs/fullorder.graph
OUTPUT=out/fullorder_graph

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

