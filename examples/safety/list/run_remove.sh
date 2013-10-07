#Configure path to Leap
LEAP=leap

OPTIONS="--show_file_info -l log --ignore $1 -sm -yices+z3 -dp tll -co pruning"

PRG=prgs/list_remove.prg
INV_FOLDER=invs/remove
GRAPH=graphs/list_remove.graph
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -g ${GRAPH} -o ${OUTPUT}

