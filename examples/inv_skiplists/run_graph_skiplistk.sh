LEAP=../../leap
OPTIONS="-fpm -sm -yices+z3 -dp tslk -co union -hp -do benchmarks"

PRG=prgs/skiplistk.prg
INV_FOLDER=invs/skiplistk
GRAPH=graphs/skiplistk.graph
OUTPUT=out/skiplistk

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

