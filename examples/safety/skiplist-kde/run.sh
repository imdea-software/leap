#Configure path to Leap
LEAP=leap

OPTIONS="--focus $1 -co union -sm -yices+z3 -dp tsl"

PRG=prgs/skiplist-kde.prg
INV_FOLDER=invs
GRAPH=graphs/skiplist-kde.graph
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

