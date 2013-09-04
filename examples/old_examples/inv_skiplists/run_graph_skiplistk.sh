LEAP=../../leap
OPTIONS="-fpm -sm -yices+z3 -dp tslk[3] -co union -hp -do benchmarks --show_file_info"

PRG=prgs/skiplistk.prg
INV_FOLDER=invs/skiplistk
GRAPH=graphs/skiplistk.graph
OUTPUT=out/skiplistk

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

