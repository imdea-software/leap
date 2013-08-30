
global
    addr head
    addr tail
    ghost addrSet region
//  ghost elemSet elements

assume
  region = {head} Union {tail} Union {null} /\
//  skiplist(heap, region, 0, head, tail) /\
  orderlist (heap, head, tail) /\
  region = addr2set (heap, head, 0) /\
  tail->nextat[0] = null /\

  head->nextat[0] = tail /\

  rd(heap, head).data = lowestElem /\
  rd(heap, tail).data = highestElem /\
  head != tail /\
  head != null /\
  tail != null


// ----- PROGRAM BEGINS --------------------------------------
                            
                              procedure main ()
                                elem e
                              begin
:main_body[
                                while (true) do
                                  // Generate random e
                                  e := havocSLElem();
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


                              procedure search (e:elem)
                                int i
                                addr prev
                                addr curr
                              begin
                                i := 0;
                                prev := head;
                                curr := prev->nextat[i];
                                while (0 <= i /\ curr->data != e) do
                                  curr := prev->nextat[i];
                                  while (curr->data < e) do
                                    prev := curr;
                                    curr := prev->nextat[i];
                                  endwhile
                                  i := i -1;
                                endwhile
                                return(); //return (curr->data = v)
                              end

// ----- INSERT ----------------------------------------------


                              procedure insert (e:elem)
                                addrarr update
                                addr prev
                                addr curr
                                addr newCell
                                int lvl
                                int i
                                bool valueWasIn := false
                                bool all_processed := false

                              begin
:insert_body[
:insert_valueWasIn_false[
:insert_not_all_processed_one[
                                lvl := 0;
                                prev := head;
:insert_prev_in_region[
:insert_prev_is_head[
                                curr := prev->nextat[0];
:insert_curr_in_region[
:insert_set_i
                                i := 0;
:insert_valueWasIn_false]
:insert_prev_is_head]
:insert_lookup_loop[
:insert_prev_next_region_one[
                                while (0 <= i) do
                                  curr := prev->nextat[i];
:insert_prev_next_region_one]
:insert_prev_next_curr_one[
                                  while (curr != null /\ curr->data < e) do
:insert_lookup_inside[
                                    prev := curr;
:insert_prev_next_curr_one]
:insert_prev_next_region_two
                                    curr := prev->nextat[i];
:insert_lookup_inside]
                                  endwhile
:insert_prev_next_curr_two[
                                  update[i] := prev;
:insert_update_set
                                  i := i - 1;
:insert_prev_next_curr_two]
:insert_prev_next_region_three
                                  valueWasIn := (curr->data = e); // skip;
:insert_lookup_loop]
                                endwhile
:insert_update_all_set[
:insert_final_if_condition
                                if (~ (valueWasIn)) then
:insert_final_if[
:insert_update_all_bounds[
                                  newCell := mallocSLK(e,lvl);
:insert_newCell_created[
:insert_i_set_zero
                                  i := 0;
:insert_update_all_bounds]
:insert_update_upper_bounds[
:insert_newCell_disconnected[
:insert_final_loop[
:insert_not_all_processed_one]
                                  while (~ (all_processed)) do
:insert_not_all_processed_two[
                                    newCell->nextat[i] := update[i]->nextat[i];
:insert_newCell_next_connected
                                    update[i]->nextat[i] := newCell
                                      $ if (i=0) then
                                          region := region Union {newCell};
                                        endif
                                      $
:insert_newCell_disconnected]
:insert_newCell_connected[
                                    if (i=lvl) then
:insert_i_upper_limit
                                      all_processed := true;
                                    endif
:insert_not_all_processed_two]
:insert_update_upper_bounds]
:insert_increase_i
                                    i := i + 1;
:insert_newCell_connected]
                                  endwhile
:insert_final_loop]
:insert_newCell_created]
:insert_final_if]
                                endif
:insert_update_all_set]
:insert_prev_in_region]
:insert_curr_in_region]
                                return (); // return (~ valueWasIn)
:insert_body]
                              end

// ----- REMOVE ----------------------------------------------


                              procedure remove (e:elem)
                                addrarr update
                                int removeFrom := 0
                                int i
                                addr prev
                                addr curr
                                bool valueWasIn
                                bool all_processed := false
                              begin
:remove_body[
                                prev := head;
:remove_prev_is_head[
:remove_prev_in_region[
                                curr := prev->nextat[0];
:remove_curr_in_region[
:remove_curr_not_null[
                                i := 0;
:remove_bounded_prev[
:remove_prev_is_head]
:remove_prev_next_region_one[
:remove_lookup_loop[
                                while (i >= 0) do
                                  curr := prev->nextat[i];
:remove_prev_next_region_one]
:remove_prev_next_curr[
                                  while (curr != null /\ curr->data < e) do
:remove_curr_lower_e
                                    prev := curr;
:remove_prev_next_curr]
:remove_prev_eq_curr
                                    curr := prev->nextat[i];
                                  endwhile
:remove_bounded_curr[
                                  if (curr != null /\ curr->data != e) then
                                    removeFrom := i - 1;
                                  endif
                                  update[i] := prev;
:remove_lookup_i_decreases
                                  i := i - 1;
:remove_bounded_curr]
                                endwhile
:remove_lookup_loop]
:remove_section[
:remove_set_valueWasIn
:remove_update_next_all_greater[
                                valueWasIn := curr->data = e; // skip;
:remove_prev_in_region]
:remove_bounded_prev]
:remove_final_conditional[
                                if (valueWasIn) then
:remove_final_if_true[
                                  i := removeFrom;
:remove_update_next_all_greater]
:remove_curr_in_region]
:remove_final_loop[
:remove_final_while_begins[
                                  while (~ (all_processed)) do
:remove_final_loop_inside[
:remove_not_all_processed[
                                    update[i]->nextat[i] := curr->nextat[i]
                                    $ if (i=0) then
                                        region := region SetDiff {curr};
                                      endif
                                    $
:remove_final_while_begins]
:remove_newCell_connected[
                                    if (i=0) then
:remove_i_lower_limit
                                      all_processed := true;
                                    endif
:remove_not_all_processed]
:remove_final_loop_i_decreases
                                    i := i - 1;
:remove_newCell_connected]
:remove_final_loop_inside]
                                  endwhile
:remove_final_loop]
:remove_final_if_true]
                                endif
:remove_final_conditional]
:remove_section]
:remove_curr_not_null]
                              return (); // return (valueWasIn)
:remove_body]
                              end
                            
