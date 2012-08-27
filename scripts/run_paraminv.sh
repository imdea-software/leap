# P-INV over activelow
echo "==  P-INV activelow  ================================================================";
time ../leap ../examples/prg/ticketint.prg -dp num \
      -i ../examples/inv_cand/ticketint_activelow.inv -pinv \
      -o ../examples/out/vc_ticketint_pinv_activelow.out;
echo "==  P-INV activelow  ================================================================";


# P-INV over notsame (2 vc remains unverified)
echo "==  P-INV notsame  ==================================================================";
time ../leap ../examples/prg/ticketint.prg -dp num \
      -i ../examples/inv_cand/ticketint_notsame.inv -pinv \
      -o ../examples/out/vc_ticketint_pinv_notsame.out;
echo "==  P-INV notsame  ==================================================================";


# SP-INV over notsame using activelow as support
echo "==  SP-INV notsame (activelow)  =====================================================";
time ../leap ../examples/prg/ticketint.prg -dp num \
      -i ../examples/inv_cand/ticketint_notsame.inv \
      -spinv ../examples/inv_cand/ticketint_activelow.inv \
      -o ../examples/out/vc_ticketint_spinv_notsame.out;
echo "==  SP-INV notsame (activelow)  =====================================================";


# P-INV minticket (1 vc remains unverified)
echo "==  P-INV minticket  ================================================================";
time ../leap ../examples/prg/ticketint.prg -dp num \
      -i ../examples/inv_cand/ticketint_minticket.inv -pinv \
      -o ../examples/out/vc_ticketint_pinv_minticket.out;
echo "==  P-INV minticket  ================================================================";


# SP-INV over minticket using activelow and notsame as support
echo "==  SP-INV minticket (notsame)  =====================================================";
time ../leap examples/prg/ticketint.prg -dp num \
      -i ../examples/inv_cand/ticketint_minticket.inv \
      -spinv ../examples/inv_cand/ticketint_notsame.inv \
      -o ../examples/out/vc_ticketint_spinv_minticket.out;
echo "==  SP-INV minticket (notsame)  =====================================================";


# P-INV mutex (1 vc remains unverified)
echo "==  P-INV mutex  ====================================================================";
time ../leap ../examples/prg/ticketint.prg -dp num \
      -i ../examples/inv_cand/ticketint_mutex.inv -pinv \
      -o ../examples/out/vc_ticketint_pinv_mutex.out;
echo "==  P-INV mutex  ====================================================================";


# SP-INV mutex using minticket and notsame as support
echo "==  SP-INV mutex (minticket, notsame)  ==============================================";
time ../leap ../examples/prg/ticketint.prg -dp num \
      -i ../examples/inv_cand/ticketint_mutex.inv \
      -spinv ../examples/inv_cand/ticketint_minticket.inv,../examples/inv_cand/ticketint_notsame.inv \
      -o ../examples/out/vc_ticketint_spinv_mutex.out;
echo "==  SP-INV mutex (minticket, notsame)  ==============================================";



# P-INV over activelow
echo "==  P-INV activelow  ================================================================";
time ../leap ../examples/prg/ticketset.prg -dp num \
      -i ../examples/inv_cand/ticketset_activelow.inv -pinv \
      -o ../examples/out/vc_ticketset_pinv_activelow.out;
echo "==  P-INV activelow  ================================================================";


# P-INV over notsame (2 vc remains unverified)
echo "==  P-INV notsame  ==================================================================";
time ../leap ../examples/prg/ticketset.prg -dp num \
      -i ../examples/inv_cand/ticketset_notsame.inv -pinv \
      -o ../examples/out/vc_ticketset_pinv_notsame.out;
echo "==  P-INV notsame  ==================================================================";


# SP-INV over notsame using activelow as support
echo "==  SP-INV notsame (activelow)  =====================================================";
time ../leap ../examples/prg/ticketset.prg -dp num \
      -i ../examples/inv_cand/ticketset_notsame.inv \
      -spinv ../examples/inv_cand/ticketset_activelow.inv \
      -o ../examples/out/vc_ticketset_spinv_notsame.out;
echo "==  SP-INV notsame (activelow)  =====================================================";


# P-INV minticket (1 vc remains unverified)
echo "==  P-INV minticket  ================================================================";
time ../leap ../examples/prg/ticketset.prg -dp num \
      -i ../examples/inv_cand/ticketset_minticket.inv -pinv \
      -o ../examples/out/vc_ticketset_pinv_minticket.out;
echo "==  P-INV minticket  ================================================================";


# SP-INV over minticket using activelow and notsame as support
echo "==  SP-INV minticket (notsame)  =====================================================";
time ../leap ../examples/prg/ticketset.prg -dp num \
      -i ../examples/inv_cand/ticketset_minticket.inv \
      -spinv ../examples/inv_cand/ticketset_notsame.inv,../examples/inv_cand/ticketset_activelow.inv
      -o ../examples/out/vc_ticketset_spinv_minticket.out;
echo "==  SP-INV minticket (notsame)  =====================================================";


# P-INV mutex (1 vc remains unverified)
echo "==  P-INV mutex  ====================================================================";
time ../leap ../examples/prg/ticketset.prg -dp num \
      -i ../examples/inv_cand/ticketset_mutex.inv -pinv \
      -o ../examples/out/vc_ticketset_pinv_mutex.out;
echo "==  P-INV mutex  ====================================================================";


# SP-INV mutex using minticket and notsame as support
echo "==  SP-INV mutex (minticket, notsame)  ==============================================";
time ../leap ../examples/prg/ticketset.prg -dp num \
      -i ../examples/inv_cand/ticketset_mutex.inv \
      -spinv ../examples/inv_cand/ticketset_minticket.inv,../examples/inv_cand/ticketset_notsame.inv \
      -o ../examples/out/vc_ticketset_spinv_mutex.out;
echo "==  SP-INV mutex (minticket, notsame)  ==============================================";
