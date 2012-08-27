##
#
# Parametrized invariance example for lock-coupling lists with add method only
#
##

LEAP=../../leap
LEAP_OPTIONS="--show -dp tll --show_file_info -co union -hp"

PRG=lock_coupling_lists_simple.prg
INV_FOLDER=inv_cand
OUT_FOLDER=out



#=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=


### lock_coupling_lists_region.inv:
#
#
#    head in region
# /\ tail in region
# /\ @prev_def(i). -> insert::prev(i) in region
# /\ @curr_def(i). -> insert::curr(i) in region
# /\ (@12(i). \/ @13(i).) -> ~ (insert::aux(i) in region)
# /\ null in region
# /\ region = addr2set(heap, head)
#
#
# Examples: (VERIFIES HOPEFULLY)
#
echo "==  P-INV lock_coupling_lists_region ==================================================";
time $LEAP $LEAP_OPTIONS -z3 $PRG -i $INV_FOLDER/lock_coupling_lists_region.inv -pinv+ -o $OUT_FOLDER/lock_coupling_list_region_pinv.out
echo "==  P-INV lock_coupling_lists_region ==================================================";


#=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=


### lock_coupling_lists_disj.inv:
#
#
# (i != j /\ @after_new(i). /\ @after_new(j).) -> insert::aux(i) != insert::aux(j)
#
#
# Examples: (VERIFIES HOPEFULLY)
#
#echo "==  P-INV lock_coupling_lists_disj ==================================================";
#time $LEAP $LEAP_OPTIONS -z3 $PRG -i $INV_FOLDER/lock_coupling_lists_disj.inv -pinv+ -o $OUT_FOLDER/lock_coupling_list_disj_pinv.out
#echo "==  P-INV lock_coupling_lists_disj ==================================================";


#=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=


### lock_coupling_lists_support.inv:
#
# 
#   head != null
# /\ tail != null
# /\ head != tail
# /\ @12(i). -> (    insert::aux(i) != head
#                 /\ insert::aux(i) != tail
#                 /\ insert::aux(i) != insert::prev(i)
#                 /\ insert::aux(i) != insert::curr(i))
# /\ rd(heap, head).next != head
# /\ @3(i). -> insert::prev(i) != rd(heap, insert::prev(i)).next
# /\ (@1(i). \/ @2(i). \/ @3(i).) -> rd(heap, head).next != head
# /\ (@2(i). \/ @3(i). \/ @4(i).) -> insert::prev(i) = head
# /\ (@6(i). \/ @7(i). \/ @8(i).) -> insert::curr(i) != null
# 
# // For transition 8
# /\ (insert::curr(i) = null \/ (insert::curr(i) != null /\ rd(heap, insert::curr(i)).next != insert::curr(i)))
#
#
# Examples: (VERIFIES)
#
#echo "==  P-INV lock_coupling_lists_support ==================================================";
#time $LEAP $LEAP_OPTIONS $PRG -z3 -i $INV_FOLDER/lock_coupling_lists_support.inv -spinv $INV_FOLDER/lock_coupling_lists_region.inv,$INV_FOLDER/lock_coupling_lists_disj.inv -o $OUT_FOLDER/lock_coupling_list_support_spinv.out
#echo "==  P-INV lock_coupling_lists_support ==================================================";


#=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=


### lock_coupling_lists_next.inv:
#
#
#    (@equals(i). -> insert::prev(i) = insert::curr(i))
# /\ ((@follows(i). /\ ~ @equals(i).) -> (insert::prev(i) != insert::curr(i) /\ rd(heap,insert::prev(i)).next = insert::curr(i)))
# /\ (@diff(i). -> insert::prev(i) != insert::curr(i))
#
#
# Examples: (VERIFIES)
#
#echo "==  SP-INV lock_coupling_lists_next ==================================================";
#time $LEAP $LEAP_OPTIONS -z3 $PRG -i $INV_FOLDER/lock_coupling_lists_next.inv -spinv $INV_FOLDER/lock_coupling_lists_support.inv -o $OUT_FOLDER/lock_coupling_list_next_spinv.out
#echo "==  SP-INV lock_coupling_lists_next ==================================================";


#=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=


# (DEEPRECATED)
### lock_coupling_lists_owns.inv:
#
#
# ((@owns_prev_one(i). \/ @owns_prev_two(i).) -> rd(heap, insert::prev(i)).lockid = i) /\
# ((@owns_curr_one(i). \/ @owns_curr_two(i).) -> rd(heap, insert::curr(i)).lockid = i)
#
#
# Examples: (VERIFIES)
#
#echo "==  SP-INV lock_coupling_lists_owns ==================================================";
#time $LEAP $LEAP_OPTIONS -z3 $PRG -i $INV_FOLDER/lock_coupling_lists_owns.inv -spinv $INV_FOLDER/lock_coupling_lists_next.inv -o $OUT_FOLDER/lock_coupling_list_owns_spinv.out
#echo "==  SP-INV lock_coupling_lists_owns ==================================================";


#=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=


### lock_coupling_lists_preserve.inv:
#
#
#    null in addr2set(heap, head) /\ region = path2set(getp (heap, head, null))
#
#
# Examples: (VERIFIES)
#
#echo "==  P-INV lock_coupling_lists_region ==================================================";
#time $LEAP $LEAP_OPTIONS -z3 $PRG -i $INV_FOLDER/lock_coupling_lists_preserve.inv -spinv $INV_FOLDER/lock_coupling_lists_region.inv -o $OUT_FOLDER/lock_coupling_list_preserve_spinv.out
#echo "==  P-INV lock_coupling_lists_region ==================================================";
