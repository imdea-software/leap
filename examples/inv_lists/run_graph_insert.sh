LEAP=../../leap
OPTIONS="-z3 -dp tll -co union -hp"

PRG=prgs/listInsert.prg
INV_FOLDER=invs/insert_invs
GRAPH=graphs/insert.graph
OUTPUT=out/insert_graph

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

