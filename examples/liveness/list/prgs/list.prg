
global
  addr head
  addr tail
  ghost addrSet region
  ghost elemSet elements
  ghost tidSet aheadSet
  ghost tidSet aheadInsert
  ghost tidSet insideSet
  ghost tidSet insideInsert
//  ghost bool kisinm

assume
  region = union (union ({head}, {tail}), {null}) /\
  elements = eunion (esingle (rd(heap,head).data),
                     esingle (rd(heap,tail).data)) /\
  // or orderlist (heap, head, null)
  rd(heap, head).data = lowestElem /\
  rd(heap, tail).data = highestElem /\
  rd(heap, head).lockid = # /\
  rd(heap, tail).lockid = # /\
  head != tail /\
  head != null /\
  tail != null /\
  head->next = tail /\
  tail->next = null
//  ~ (kisinm)


// ----- PROGRAM BEGINS --------------------------------------
                            
                              procedure main ()
                                elem e
                              begin
:main_body[
                                while (true) do
                                  // Generate random e
                                  e := havocListElem();
:main_e[
                                  choice
                                    call search(e);
                                  _or_
                                    call insert(e);
                                  _or_
                                    call remove(e);
                                  endchoice
                                endwhile
                                return ();
:main_e]
:main_body]
                              end

// ----- SEARCH ----------------------------------------------


                              procedure search (e:elem) : bool
                                addr prev
                                addr curr
                                addr aux
                                bool result

                              begin
:search_body[
:sch_init_no_lock[
                                prev := head;
:sch_prev_lower[
:sch_prev_def[
:sch_prev_is_head[
                                prev->lock
                                  $
                                    insideSet := tunion (insideSet, tsingle(me));
                                  $
:sch_init_no_lock]
:sch_owns_prev[
:sch_got_lock[
:sch_working[
:sch_init_prev_locked[
                                curr := prev->next;
:sch_curr_def[
:sch_follows[
                                curr->lock;
:sch_init_prev_locked]
:sch_prev_is_head]
:sch_owns_curr_one[
:sch_prev_curr_locked[
                                while (curr->data < e) do
:sch_while_begins[
                                  aux := prev;
:sch_aux_eq_prev
                                  prev := curr;
:sch_prev_curr_locked]
:sch_equals[
:sch_aux_before_prev
                                  aux->unlock;
:sch_only_curr_locked
                                  curr := curr->next;
:sch_while_begins]
:sch_equals]
:sch_owns_curr_one]
:sch_only_prev_locked
                                  curr->lock;
:sch_owns_curr_two[
                                endwhile
:sch_after_lookup
                                result := curr->data = e;
:sch_prev_lower]
:sch_result_set[
:sch_diff[
:sch_last_prev_unlock
                                prev->unlock;
:sch_owns_prev]
:sch_follows]
:sch_prev_def]
:sch_releases_last_lock
                                curr->unlock
                                  $
                                    insideSet := tdiff (insideSet, tsingle(me));
                                    aheadSet := tdiff (aheadSet, tsingle(me));
                                  $
:sch_owns_curr_two]
:sch_diff]
:sch_curr_def]
:sch_got_lock]
:sch_working]
:sch_return
                                return (result);
:sch_result_set]
:search_body]
                              end

// ----- INSERT ----------------------------------------------


                              procedure insert (e:elem)
                                addr prev
                                addr curr
                                addr aux

                              begin
:insert_body[
:ins_head_next_diff[
:ins_init_no_lock[
                                prev := head;
:ins_prev_lower[
:ins_prev_def[
:ins_prev_is_head[
:ins_gets_first_lock
                                prev->lock
                                  $
                                    insideSet := tunion (insideSet, tsingle(me));
                                    insideInsert := tunion (insideInsert, tsingle(me));
                                    if (me = k) then
																			aheadSet := insideSet;
																			aheadInsert := insideInsert;
																		endif
                                  $
:ins_init_no_lock]
:ins_working[
:ins_owns_prev[
:ins_prev_locked_one[
:ins_init_prev_locked[
                                curr := prev->next;
:ins_head_next_diff]
:ins_curr_def[
:ins_follows[
                                curr->lock;
//                                  $
//                                    if (me = k) then kisinm := true; endif
//                                  $
:ins_init_prev_locked]
:ins_prev_is_head]
:ins_owns_curr_one[
:ins_lookup_loop[
:ins_lookup_condition
:ins_prev_curr_locked[
                                while (curr->data < e) do
:ins_while_begins[
:ins_while[
                                  aux := prev;
:ins_prev_locked_one]
:ins_aux_eq_prev
                                  prev := curr;
:ins_prev_locked_two[
:ins_prev_curr_locked]
:ins_equals[
:ins_aux_before_prev
                                  aux->unlock;
:ins_only_curr_locked
                                  curr := curr->next;
:ins_while_begins]
:ins_equals]
:ins_while]
:ins_owns_curr_one]
:ins_lock_curr
                                  curr->lock;
:ins_owns_curr_two[
                                endwhile
:ins_prev_locked_two]
:ins_lookup_loop]
:ins_insertion_process[
:ins_final_conditional
                                if (curr != null /\ curr->data > e) then
:ins_insert[
                                  aux := malloc(e, null, #);
:after_malloc[
                                  aux->next := curr;
:ins_aux_before_curr
:ins_diff[
                                  prev->next := aux
                                    $
                                      elements := eunion (elements, esingle(e));
                                      region := union (region, {aux});
                                      insideInsert := tdiff (insideInsert, tsingle(me));
                                      aheadInsert := tdiff (aheadInsert, tsingle(me));
                                    $
:after_malloc]
:ins_insert]
:ins_prev_lower]
                                endif
:ins_elem_inserted[
:ins_last_prev_unlock
                                prev->unlock;
:ins_owns_prev]
:ins_prev_def]
:ins_insertion_process]
:ins_diff]
:ins_releases_last_lock
                                curr->unlock
                                  $
                                    insideSet := tdiff (insideSet, tsingle(me));
                                    aheadSet := tdiff (aheadSet, tsingle(me));
//                                    if (me = k) then
//                                      kisinm := false;
//                                    endif
                                  $
:ins_follows]
:ins_owns_curr_two]
:ins_curr_def]
:ins_working]
:ins_return
                                return();
:ins_elem_inserted]
:insert_body]
                              end

// ----- REMOVE ----------------------------------------------


                              procedure remove (e:elem)
                                addr prev
                                addr curr
                                addr aux

                              begin
:remove_body[
:rem_init_no_lock[
                                prev := head;
:rem_prev_lower[
:rem_prev_def[
:rem_prev_is_head[
                                prev->lock
                                  $
                                    insideSet := tunion (insideSet, tsingle(me));
                                  $
:rem_init_no_lock]
:rem_working[
:rem_owns_prev[
:rem_got_lock[
:rem_init_prev_locked[
                                curr := prev->next;
:rem_curr_def[
:rem_follows[
                                curr->lock;
:rem_init_prev_locked]
:rem_prev_is_head]
:rem_owns_curr_one[
:rem_lookup_loop[
:rem_prev_curr_locked[
                                while (curr->data < e) do
:rem_while_begins[
:rem_while[
                                  aux := prev;
:rem_aux_eq_prev
                                  prev := curr;
:rem_prev_curr_locked]
:rem_equals[
:rem_aux_before_prev
                                  aux->unlock;
:rem_only_curr_locked
                                  curr := curr->next;
:rem_while_begins]
:rem_equals]
:rem_while]
:rem_owns_curr_one]
:rem_lock_curr
                                  curr->lock;
:rem_owns_curr_two[
                                endwhile
:rem_lookup_loop]
:rem_final_conditional
                                if (curr->data = e) then
:rem_remove[
:rem_if_one
                                  aux := curr->next;
:rem_if_two
                                  prev->next := aux
                                    $
                                      elements := ediff (elements, esingle(e));
                                      region := diff (region, {curr});
                                    $
:rem_follows]
:rem_curr_def]
:rem_remove]
:rem_prev_lower]
:rem_releases_curr_one
																	curr->unlock;
:rem_owns_curr_two]
																else
:rem_releases_curr_two
																	curr->unlock;
                                endif
:rem_elem_removed[
:rem_diff[
:rem_last_prev_unlock
																prev->unlock
																	$
																		insideSet := tdiff (insideSet, tsingle(me));
                                    aheadSet := tdiff (aheadSet, tsingle(me));
																	$
:rem_owns_prev]
:rem_prev_def]
//:rem_releases_last_lock
//																curr->unlock;
:rem_diff]
:rem_got_lock]
:rem_working]
:rem_return
                                return();
:rem_elem_removed]
:remove_body]
                              end
                            
