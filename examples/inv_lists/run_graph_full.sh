LEAP=../../leap
OPTIONS="-fpm -sm -yices+z3 -dp tll -co union -hp -do benchmarks/full+fpm+cases"

PRG=prgs/list.prg
INV_FOLDER=invs/full_invs
GRAPH=graphs/full.graph
OUTPUT=out/full_graph

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

