##
#
# Parametrized invariance example for ticket program using integers
#
##

LEAP=../../leap
LEAP_OPTIONS="--show_file_info --show -dp num"

PRG=ticketset_vd.prg
PVD=ticketset.pvd
FORMULA=ticketset.frm
INV_FOLDER=inv_support
OUT=out/ticketset_pvd.out

time $LEAP $LEAP_OPTIONS $PRG -pvd $PVD -f $FORMULA -o $OUT
