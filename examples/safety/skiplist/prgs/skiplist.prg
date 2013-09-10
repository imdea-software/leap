
global
    int maxLevel
    addr head
    addr tail
    ghost addrSet region
    ghost elemSet elements

assume
  region = {head} Union {tail} Union {null} /\
  elements = UnionElem (SingleElem (lowestElem),
                        SingleElem (highestElem)) /\
//  elements = UnionElem (
//              UnionElem (SingleElem (rd(heap,head).data),
//                         SingleElem (rd(heap,tail).data)),
//                         SingleElem (rd(heap,null).data)) /\
  skiplist(heap, region, 0, head, tail, elements) /\
  rd(heap, head).data = lowestElem /\
  rd(heap, tail).data = highestElem /\
  head != tail /\
  head != null /\
  tail != null /\
  head->arr[0] = tail /\
  maxLevel = 0


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
                                i := maxLevel;
                                prev := head;
                                curr := prev->arr[i];
                                while (0 <= i /\ curr->data != e) do
                                  curr := prev->arr[i];
                                  while (curr->data < e) do
                                    prev := curr;
                                    curr := prev->arr[i];
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

                              begin
:insert_body[
:insert_valueWasIn_false[
                                lvl := havocLevel();
                                if (lvl > maxLevel) then
:insert_lvl_outrange[
                                  i := maxLevel + 1;
:insert_i_greater_maxLevel[
:insert_test_i_lower_lvl
                                  while (i <= lvl) do
:insert_i_lesseq_lvl_one[
:insert_i_top_maxLevel[
                                    head->arr[i] := tail;
:insert_head_next_i_tail[
                                    tail->arr[i] := null;
:insert_tail_next_i_null[
                                    maxLevel := i;
:insert_maxLevel_eq_i
:insert_i_top_maxLevel]
:insert_i_greater_maxLevel]
:insert_initial_loop_i_increases
                                    i := i + 1;
:insert_tail_next_i_null]
:insert_head_next_i_tail]
:insert_i_lesseq_lvl_one]
                                  endwhile
:insert_lvl_outrange]
                                endif
:insert_lvl_inrange[
                                prev := head;
:insert_prev_is_head[
:insert_prev_in_region[
                                curr := prev->arr[maxLevel];
:insert_lookup_loop_plus_init[
:insert_curr_not_null[
:insert_curr_in_region[
:insert_i_eq_max
                                i := maxLevel;
:insert_prev_is_head]
:insert_valueWasIn_false]
:insert_lookup_loop[
:insert_prev_next_region_one[
                                while (0 <= i) do
                                  curr := prev->arr[i];
:insert_prev_next_region_one]
:insert_prev_next_curr_one[
                                  while (curr != null /\ curr->data < e) do
:insert_curr_low
                                    prev := curr;
:insert_prev_next_curr_one]
:insert_prev_is_curr
                                    curr := prev->arr[i];
                                  endwhile
:insert_prev_next_curr_two[
                                  update[i] := prev;
:insert_update_set
                                  i := i - 1;
:insert_prev_next_curr_two]
:insert_set_valueWasIn
                                  valueWasIn := (curr->data = e); // skip;
                                endwhile
:insert_lookup_loop_plus_init]
:insert_lookup_loop]
:insert_update_all_set[
:insert_final_if_condition
                                if (~ (valueWasIn)) then
:insert_update_all_order[
                                  newCell := mallocSL(e,lvl);
:insert_newCell_created[
:insert_i_set_zero
                                  i := 0;
:insert_update_all_order]
:insert_newCell_low_connected[
:insert_update_upper_bounds[
:insert_newCell_unconnected[
                                  while (i <= lvl) do
:insert_not_all_processed[
                                    newCell->arr[i] := update[i]->arr[i];
:insert_newCell_next_connected
                                    update[i]->arr[i] := newCell
                                      $ if (i=0) then
                                          region := region Union {newCell};
                                          elements := UnionElem (elements, SingleElem(e));
                                        endif
                                      $
:insert_newCell_unconnected]
:insert_not_all_processed]
:insert_update_upper_bounds]
:insert_i_increases
                                    i := i + 1;
:insert_newCell_created]
                                  endwhile
:insert_update_all_set]
:insert_newCell_low_connected]
:insert_lvl_inrange]
:insert_prev_in_region]
:insert_curr_in_region]
                                endif
                                return (); // return (~ valueWasIn)
:insert_body]
                              end

// ----- REMOVE ----------------------------------------------


                              procedure remove (e:elem)
                                addrarr update
                                int removeFrom := maxLevel
                                int i
                                addr prev
                                addr curr
                                bool valueWasIn
                              begin
:remove_body[
                                prev := head;
:remove_prev_in_region[
:remove_prev_is_head[
                                curr := prev->arr[maxLevel];
:remove_curr_in_region[
:remove_curr_not_null[
                                i := maxLevel;
:remove_bounded_prev[
:remove_lookup_loop[
:remove_prev_is_head]
:remove_prev_next_region[
                                while (i >= 0) do
                                  curr := prev->arr[i];
:remove_prev_next_region]
:remove_prev_next_curr[
                                  while (curr != null /\ curr->data < e) do
:remove_curr_lower_e
                                    prev := curr;
:remove_prev_next_curr]
:remove_prev_is_curr
                                    curr := prev->arr[i];
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
:remove_curr_not_null]
:remove_section[
:remove_update_next_all_greater[
:remove_set_valueWasIn
                                valueWasIn := curr->data = e; // skip;
:remove_bounded_prev]
:remove_final_if[
:remove_prev_in_region]
                                if (valueWasIn) then
:remove_section_true[
                                  i := removeFrom;
:remove_update_next_all_greater]
:remove_curr_in_region]
:remove_final_loop[
:remove_final_loop_begins[
                                  while (i >= 0) do
:remove_final_loop_inside[
                                    update[i]->arr[i] := curr->arr[i]
                                    $ if (i=0) then
                                        region := region SetDiff {curr};
                                        elements := SetDiffElem (elements, SingleElem(e));
                                      endif
                                    $
:remove_final_loop_begins]
:remove_final_loop_i_decreases
                                    i := i - 1;
:remove_final_loop_inside]
                                  endwhile
:remove_final_loop]
                                endif
:remove_section_true]
:remove_section]
                                return (); // return (valueWasIn)
:remove_final_if]
:remove_body]
                              end
                            
