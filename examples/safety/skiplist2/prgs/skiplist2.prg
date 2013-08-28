
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
  tail->nextat[1] = null /\
  (addr2set(heap, head, 1)) subseteq (addr2set(heap, head, 0)) /\

  head->nextat[0] = tail /\
  head->nextat[1] = tail /\

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
                                i := 1;
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

                              begin
:insert_body[
                                choice
                                  lvl := 0;
                                _or_
                                  lvl := 1;
                                endchoice
                                prev := head;
                                curr := prev->nextat[1];
                                i := 1;
                                while (0 <= i) do
                                  curr := prev->nextat[i];
                                  while (curr != null /\ curr->data < e) do
                                    prev := curr;
                                    curr := prev->nextat[i];
                                  endwhile
                                  update[i] := prev;
                                  i := i - 1;
                                  valueWasIn := (curr->data = e); // skip;
                                endwhile
:insert_update_all_set[
:insert_update_all_bounds[
                                if (~ (valueWasIn)) then
:insert_final_if[
                                  newCell := mallocSLK(e,lvl);
:insert_newCell_created[
                                  i := 0;
:insert_update_all_bounds]
:insert_update_upper_bounds[
                                  while (i <= lvl) do
:insert_newCell_disconnected[
                                    newCell->nextat[i] := update[i]->nextat[i];
:insert_newCell_next_connected
                                    update[i]->nextat[i] := newCell
                                      $ if (i=0) then
                                          region := region Union {newCell};
                                        endif
                                      $
:insert_update_upper_bounds]
:insert_newCell_disconnected]
                                    i := i + 1;
                                  endwhile
:insert_newCell_created]
:insert_final_if]
                                endif
:insert_update_all_set]
                                return (); // return (~ valueWasIn)
:insert_body]
                              end

// ----- REMOVE ----------------------------------------------


                              procedure remove (e:elem)
                                addrarr update
                                int removeFrom := 1
                                int i
                                addr prev
                                addr curr
                                bool valueWasIn
                              begin
:remove_body[
                                prev := head;
                                curr := prev->nextat[1];
:remove_curr_not_null[
                                i := 1;
                                while (i >= 0) do
                                  curr := prev->nextat[i];
                                  while (curr != null /\ curr->data < e) do
                                    prev := curr;
                                    curr := prev->nextat[i];
                                  endwhile
                                  if (curr != null /\ curr->data != e) then
                                    removeFrom := i - 1;
                                  endif
                                  update[i] := prev;
                                  i := i - 1;
                                endwhile
:remove_section[
                                valueWasIn := curr->data = e; // skip;
:remove_final_conditional[
                                if (valueWasIn) then
:remove_final_if_true[
                                  i := removeFrom;
:remove_final_loop[
:remove_final_while_begins[
                                  while (i >= 0) do
:remove_final_loop_inside[
                                    update[i]->nextat[i] := curr->nextat[i]
                                    $ if (i=0) then
                                        region := region SetDiff {curr};
                                      endif
                                    $
:remove_final_while_begins]
                                    i := i - 1;
:remove_final_loop_inside]
                                  endwhile
:remove_final_loop]
:remove_final_if_true]
                                endif
:remove_final_conditional]
:remove_section]
                              return (); // return (valueWasIn)
:remove_curr_not_null]
:remove_body]
                              end
                            
