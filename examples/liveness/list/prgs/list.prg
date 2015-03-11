
global
  addr head
  addr tail
  ghost addrSet region
  ghost elemSet elements
  ghost tidSet aheadSet
  ghost tidSet insideSet
  ghost bool kisin

assume
  region = {head} Union {tail} Union {null} /\
  elements = UnionElem (SingleElem (rd(heap,head).data),
                        SingleElem (rd(heap,tail).data)) /\
  // or orderlist (heap, head, null)
  rd(heap, head).data = lowestElem /\
  rd(heap, tail).data = highestElem /\
  head != tail /\
  head != null /\
  tail != null /\
  head->next = tail /\
  tail->next = null


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
                                prev := head;
:sch_prev_lower[
:sch_prev_def[
:sch_prev_is_head[
                                prev->lock;
:sch_owns_prev[
:sch_got_lock[
:sch_working[
                                curr := prev->next;
:sch_curr_def[
:sch_follows[
                                curr->lock;
:sch_prev_is_head]
:sch_owns_curr_one[

                                while (curr->data < e) do
:sch_while_begins[
                                  aux := prev;
:sch_aux_eq_prev
                                  prev := curr;
:sch_equals[
:sch_aux_before_prev
                                  aux->unlock;
                                  curr := curr->next;
:sch_while_begins]
:sch_equals]
:sch_owns_curr_one]
                                  curr->lock;
:sch_owns_curr_two[
                                endwhile
:sch_after_lookup
                                result := curr->data = e;
:sch_prev_lower]
:sch_result_set[
:sch_diff[
                                prev->unlock;
:sch_owns_prev]
:sch_follows]
:sch_prev_def]
:sch_releases_last_lock
                                curr->unlock;
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
                                prev := head;
:ins_prev_lower[
:ins_prev_def[
:ins_prev_is_head[
                                prev->lock;
:ins_working[
:ins_owns_prev[
:ins_prev_advance[
                                curr := prev->next;
:ins_head_next_diff]
:ins_curr_def[
:ins_follows[
                                curr->lock;
:ins_prev_is_head]
:ins_owns_curr_one[
:ins_lookup_loop[
:ins_lookup_condition
                                while (curr->data < e) do
:ins_while_begins[
:ins_while[
                                  aux := prev;
:ins_aux_eq_prev
                                  prev := curr;
:ins_equals[
:ins_aux_before_prev
                                  aux->unlock;
                                  curr := curr->next;
:ins_prev_advance]
:ins_while_begins]
:ins_equals]
:ins_while]
:ins_owns_curr_one]
:ins_lock_curr
                                  curr->lock;
:ins_owns_curr_two[
                                endwhile
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
                                      elements := UnionElem (elements, SingleElem(e));
                                      region := region Union {aux};
                                    $
:ins_follows]
:after_malloc]
:ins_insert]
:ins_prev_lower]
                                endif
:ins_elem_inserted[
                                prev->unlock;
:ins_owns_prev]
:ins_prev_def]
:ins_releases_last_lock
                                curr->unlock;
:ins_owns_curr_two]
:ins_curr_def]
:ins_diff]
:ins_insertion_process]
:ins_return
                                return();
:ins_working]
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
                                prev := head;
:rem_prev_lower[
:rem_prev_def[
:rem_prev_is_head[
                                prev->lock;
:rem_owns_prev[
:rem_got_lock[
                                curr := prev->next;
:rem_curr_def[
:rem_follows[
                                curr->lock;
:rem_prev_is_head]
:rem_owns_curr_one[
:rem_lookup_loop[
:rem_working[
                                while (curr->data < e) do
:rem_while_begins[
:rem_while[
                                  aux := prev;
:rem_aux_eq_prev
                                  prev := curr;
:rem_equals[
:rem_aux_before_prev
                                  aux->unlock;
                                  curr := curr->next;
:rem_while_begins]
:rem_equals]
:rem_while]
:rem_owns_curr_one]
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
                                      elements := SetDiffElem (elements, SingleElem(e));
                                      region := region SetDiff {curr};
                                    $
:rem_follows]
:rem_curr_def]
:rem_remove]
:rem_prev_lower]
                                endif
:rem_elem_removed[
:rem_diff[
                                prev->unlock;
:rem_owns_prev]
:rem_prev_def]
:rem_releases_last_lock
                                curr->unlock;
:rem_diff]
:rem_owns_curr_two]
:rem_got_lock]
:rem_working]
:rem_return
                                return();
:rem_elem_removed]
:remove_body]
                              end
                            
