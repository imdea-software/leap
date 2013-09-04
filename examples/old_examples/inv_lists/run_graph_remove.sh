LEAP=../../leap
OPTIONS="-z3 -dp tll -co union -hp"

PRG=prgs/listRemove.prg
INV_FOLDER=invs/remove_invs
GRAPH=graphs/remove.graph
OUTPUT=out/remove_graph

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

