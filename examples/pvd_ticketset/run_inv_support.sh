##
#
# Supporting invariants for ticketset PVD
#
##

LEAP=../../leap
LEAP_OPTIONS="-dp num"

PRG=ticketset_vd.prg
INV_FOLDER=inv_support
OUT_FOLDER=out


# P-INV over activelow
echo "==  P-INV activelow  ================================================================";
time $LEAP $LEAP_OPTIONS $PRG -i $INV_FOLDER/ticketset_activelow.inv -pinv -o $OUT_FOLDER/vc_ticketset_pinv_activelow.out;
echo "==  P-INV activelow  ================================================================";


# SP-INV over notsame using activelow as support
echo "==  SP-INV notsame (activelow)  =====================================================";
time $LEAP $LEAP_OPTIONS $PRG -i $INV_FOLDER/ticketset_notsame.inv -spinv $INV_FOLDER/ticketset_activelow.inv -o $OUT_FOLDER/vc_ticketset_spinv_notsame.out;
echo "==  SP-INV notsame (activelow)  =====================================================";


# SP-INV over minticket using activelow and notsame as support
echo "==  SP-INV minticket (notsame)  =====================================================";
time $LEAP $LEAP_OPTIONS $PRG -i $INV_FOLDER/ticketset_minticket.inv -spinv $INV_FOLDER/ticketset_notsame.inv,$INV_FOLDER/ticketset_activelow.inv -o $OUT_FOLDER/vc_ticketset_spinv_minticket.out;
echo "==  SP-INV minticket (notsame)  =====================================================";


# SP-INV mutex using minticket and notsame as support
echo "==  SP-INV mutex (minticket, notsame)  ==============================================";
time $LEAP $LEAP_OPTIONS $PRG -i $INV_FOLDER/ticketset_mutex.inv -spinv $INV_FOLDER/ticketset_minticket.inv,$INV_FOLDER/ticketset_notsame.inv -o $OUT_FOLDER/vc_ticketset_spinv_mutex.out;
echo "==  SP-INV mutex (minticket, notsame)  ==============================================";

