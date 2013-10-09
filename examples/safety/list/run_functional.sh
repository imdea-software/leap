#Configure path to Leap
LEAP=leap

OPTIONS="--ignore $1 -sm -yices+z3 -dp tll -co pruning"

PRG=prgs/list_functional.prg
INV_FOLDER=invs/functional
GRAPH=graphs/list_functional.graph
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

