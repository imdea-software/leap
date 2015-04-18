#Configure path to Leap
LEAP=leap

OPTIONS="-sm -dp tll -co pruning -sf -si -v 1 -pvdconds consecution -pvdnodes n2 -focus $1"

PRG=prgs/list.prg
INV_FOLDER=invs
PVD=pvd/list.pvd
SUPP=pvd/list.supp
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -pvd ${PVD} -ps ${SUPP} -o ${OUTPUT}

