##
#
# Parametrized invariance example for ticket program using sets
#
##

LEAP=../../leap
LEAP_OPTIONS="-dp num"

PRG=ticketset.prg
INV_FOLDER=inv_cand
OUT_FOLDER=out


# P-INV over activelow
echo "==  P-INV activelow  ================================================================";
time $LEAP $LEAP_OPTIONS $PRG -i $INV_FOLDER/ticketset_activelow.inv -pinv -o $OUT_FOLDER/vc_ticketset_pinv_activelow.out;
echo "==  P-INV activelow  ================================================================";


# P-INV over notsame (2 vc remains unverified)
echo "==  P-INV notsame  ==================================================================";
time $LEAP $LEAP_OPTIONS $PRG -i $INV_FOLDER/ticketset_notsame.inv -pinv -o $OUT_FOLDER/vc_ticketset_pinv_notsame.out;
echo "==  P-INV notsame  ==================================================================";


# SP-INV over notsame using activelow as support
echo "==  SP-INV notsame (activelow)  =====================================================";
time $LEAP $LEAP_OPTIONS $PRG -i $INV_FOLDER/ticketset_notsame.inv -spinv $INV_FOLDER/ticketset_activelow.inv -o $OUT_FOLDER/vc_ticketset_spinv_notsame.out;
echo "==  SP-INV notsame (activelow)  =====================================================";


# P-INV minticket (1 vc remains unverified)
echo "==  P-INV minticket  ================================================================";
time $LEAP $LEAP_OPTIONS $PRG -i $INV_FOLDER/ticketset_minticket.inv -pinv -o $OUT_FOLDER/vc_ticketset_pinv_minticket.out;
echo "==  P-INV minticket  ================================================================";


# SP-INV over minticket using activelow and notsame as support
echo "==  SP-INV minticket (notsame)  =====================================================";
time $LEAP $LEAP_OPTIONS $PRG -i $INV_FOLDER/ticketset_minticket.inv -spinv $INV_FOLDER/ticketset_notsame.inv,$INV_FOLDER/ticketset_activelow.inv -o $OUT_FOLDER/vc_ticketset_spinv_minticket.out;
echo "==  SP-INV minticket (notsame)  =====================================================";


# P-INV mutex (1 vc remains unverified)
echo "==  P-INV mutex  ====================================================================";
time $LEAP $LEAP_OPTIONS $PRG -i $INV_FOLDER/ticketset_mutex.inv -pinv -o $OUT_FOLDER/vc_ticketset_pinv_mutex.out;
echo "==  P-INV mutex  ====================================================================";


# SP-INV mutex using minticket and notsame as support
echo "==  SP-INV mutex (minticket, notsame)  ==============================================";
time $LEAP $LEAP_OPTIONS $PRG -i $INV_FOLDER/ticketset_mutex.inv -spinv $INV_FOLDER/ticketset_minticket.inv,$INV_FOLDER/ticketset_notsame.inv -o $OUT_FOLDER/vc_ticketset_spinv_mutex.out;
echo "==  SP-INV mutex (minticket, notsame)  ==============================================";

