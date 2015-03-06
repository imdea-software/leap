#Configure path to Leap
LEAP=leap

OPTIONS="-v 1 -sm -dp pairs -co pruning -sf"

PRG=prgs/ticketset.prg
INV_FOLDER=invs
PVD=pvd/ticketset.pvd
SUPP=pvd/ticketset.supp
OUTPUT=vcs/

${LEAP} ${OPTIONS} ${PRG} -d ${INV_FOLDER} -pvd ${PVD} -ps ${SUPP} -o ${OUTPUT}

