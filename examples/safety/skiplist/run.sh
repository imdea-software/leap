#Configure path to Leap
LEAP=leap

OPTIONS="--focus $1 --show_file_info -co union -sm -yices+z3 -dp tsl"

PRG=prgs/skiplist.prg
INV_FOLDER=invs/gral
GRAPH=graphs/skiplist.graph
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

