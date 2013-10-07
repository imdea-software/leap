#Configure path to Leap
LEAP=leap

OPTIONS="-smt -sm -yices+z3 -dp tll -co pruning"

PRG=prgs/list_remove.prg
INV_FOLDER=invs/remove
GRAPH=graphs/list_remove.graph
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

