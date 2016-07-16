
global
  addr head
  addr tail
  ghost addrSet region
  ghost elemSet elements
  tid chosen
  elem chosen_e

assume
  region = union (union ({head}, {tail}), {null}) /\
  elements = eunion (esingle (rd(heap,head).data),
                     esingle (rd(heap,tail).data)) /\
  // or orderlist (heap, head, null)
  rd(heap, head).data = lowestElem /\
  rd(heap, tail).data = highestElem /\
  head != tail /\
  head != null /\
  tail != null /\
  head->next = tail /\
  tail->next = null /\

  chosen_e != lowestElem /\ chosen_e != highestElem


// ----- PROGRAM BEGINS --------------------------------------





                              procedure main ()
                                elem e
                                bool result
                              begin
:main_body[
                                while (true) do
                                  if me = chosen then
                                    result := call search(chosen_e);
:check_search
                                    skip;
                                  else
:main_other_threads[
                                    // Generate random e
                                    e := havocListElem();
:main_e[
                                    if (e != chosen_e) then
:main_e_not_chosen[
                                      skip;
                                      choice
                                        call search(e);
                                      _or_
                                        call insert(e);
                                      _or_
                                        call remove(e);
                                      endchoice
:main_other_threads]
:main_e_not_chosen]
                                      skip;
                                    endif
                                    skip;
                                  endif
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
                                curr->unlock;
:sch_owns_curr_two]
:sch_diff]
:sch_curr_def]
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
:ins_owns_prev[
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
:ins_curr_lower[
                                  aux := prev;
:ins_aux_eq_prev
                                  prev := curr;
:ins_equals[
:ins_aux_before_prev
                                  aux->unlock;
                                  curr := curr->next;
:ins_while_begins]
:ins_curr_lower]
:ins_equals]
:ins_while]
:ins_owns_curr_one]
                                  curr->lock;
:ins_owns_curr_two[
                                endwhile
:ins_lookup_loop]
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
                                curr->unlock;
:ins_owns_curr_two]
:ins_curr_def]
:ins_diff]
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
                                prev := head;
:rem_prev_lower[
:rem_prev_def[
:rem_prev_is_head[
                                prev->lock;
:rem_owns_prev[
                                curr := prev->next;
:rem_curr_def[
:rem_follows[
                                curr->lock;
:rem_prev_is_head]
:rem_owns_curr_one[
:rem_lookup_loop[
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
                                      elements := ediff (elements, esingle (e));
                                      region := diff (region, {curr});
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
                                curr->unlock;
:rem_diff]
:rem_owns_curr_two]
                                return();
:rem_elem_removed]
:remove_body]
                              end
                            
