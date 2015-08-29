#Configure path to Leap
LEAP=leap

OPTIONS="-sm -dp tll -co pruning -si -pvdconds $1 -pvdnodes $2 -focus $3 
-v 1"

PRG=prgs/list.prg
INV_FOLDER=invs
PVD=pvd/list.pvd
SUPP=pvd/list.supp
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -pvd ${PVD} -ps ${SUPP} -o ${OUTPUT}

