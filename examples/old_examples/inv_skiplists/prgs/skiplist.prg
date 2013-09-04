
global
    int maxLevel
    addr head
    addr tail
    ghost addrSet region
//  ghost elemSet elements

assume
  region = {head} Union {tail} Union {null} /\
//  elements = UnionElem (
//              UnionElem (SingleElem (rd(heap,head).data),
//                         SingleElem (rd(heap,tail).data)),
//                         SingleElem (rd(heap,null).data)) /\
  skiplist(heap, region, 0, head, tail) /\
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
                                    i := i + 1;
:insert_tail_next_i_null]
:insert_head_next_i_tail]
:insert_i_lesseq_lvl_one]
                                  endwhile
:insert_lvl_outrange]
                                endif
:insert_lvl_inrange[
                                prev := head;
:insert_prev_in_region[
:insert_prev_low[
                                curr := prev->arr[maxLevel];
:insert_curr_in_region[
:insert_i_eq_max
                                i := maxLevel;
:insert_bounded_i_one[
:insert_update_higher[
:insert_valueWasIn_false]
                                while (0 <= i) do
                                  curr := prev->arr[i];
                                  while (curr != null /\ curr->data < e) do
:insert_curr_low
                                    prev := curr;
                                    curr := prev->arr[i];
                                  endwhile
                                  update[i] := prev;
:insert_update_set
                                  i := i - 1;
                                  valueWasIn := (curr->data = e); // skip;
:insert_update_higher]
                                endwhile
:insert_bounded_i_one]
:insert_update_all_set[
                                if (~ (valueWasIn)) then
:insert_update_all_order[
                                  newCell := mallocSL(e,lvl);
:insert_newCell_created[
                                  i := 0;
:insert_update_all_order]
:insert_newCell_low_connected[
:insert_update_from_i_order[
:insert_newCell_unconnected[
                                  while (i <= lvl) do
:insert_i_lesseq_lvl_two[
                                    newCell->arr[i] := update[i]->arr[i];
                                    update[i]->arr[i] := newCell
                                      $ if (i=0) then
                                          region := region Union {newCell};
                                        endif
                                      $
:insert_newCell_unconnected]
:insert_i_lesseq_lvl_two]
:insert_update_from_i_order]
                                    i := i + 1;
:insert_newCell_created]
                                  endwhile
:insert_update_all_set]
:insert_newCell_low_connected]
:insert_prev_low]
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
:remove_update_higher_set[
:remove_prev_is_head]
                                while (i >= 0) do
                                  curr := prev->arr[i];
                                  while (curr != null /\ curr->data < e) do
                                    prev := curr;
                                    curr := prev->arr[i];
                                  endwhile
:remove_bounded_curr[
                                  if (curr != null /\ curr->data != e) then
                                    removeFrom := i - 1;
                                  endif
                                  update[i] := prev;
                                  i := i - 1;
:remove_bounded_curr]
                                endwhile
:remove_update_higher_set]
:remove_lookup_loop]
:remove_curr_not_null]
:remove_section[
                                valueWasIn := curr->data = e; // skip;
:remove_bounded_prev]
:remove_final_if[
:remove_prev_in_region]
                                if (valueWasIn) then
:remove_section_true[
                                  i := removeFrom;
:remove_final_loop[
:remove_curr_in_region]
                                  while (i >= 0) do
                                    update[i]->arr[i] := curr->arr[i]
                                    $ if (i=0) then
                                        region := region SetDiff {curr};
                                      endif
                                    $
                                    i := i - 1;
                                  endwhile
:remove_final_loop]
                                endif
:remove_section_true]
:remove_section]
                                return (); // return (valueWasIn)
:remove_final_if]
:remove_body]
                              end
                            
