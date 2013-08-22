
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
  tail->arr[0] = null /\
  tail->arr[1] = null /\
  (addr2set(heap, head, 1)) subseteq (addr2set(heap, head, 0)) /\

  head->arr[0] = tail /\
  head->arr[1] = tail /\

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
                                choice
                                  lvl := 0;
                                _or_
                                  lvl := 1;
                                endchoice
                                prev := head;
                                curr := prev->arr[1];
                                i := 1;
                                while (0 <= i) do
                                  curr := prev->arr[i];
                                  while (curr != null /\ curr->data < e) do
                                    prev := curr;
                                    curr := prev->arr[i];
                                  endwhile
                                  update[i] := prev;
                                  i := i - 1;
                                  valueWasIn := (curr->data = e); // skip;
                                endwhile
                                if (~ (valueWasIn)) then
                                  newCell := mallocSLK(e,lvl);
                                  i := 0;
                                  while (i <= lvl) do
                                    newCell->arr[i] := update[i]->arr[i];
                                    update[i]->arr[i] := newCell
                                      $ if (i=0) then
                                          region := region Union {newCell};
                                        endif
                                      $
                                    i := i + 1;
                                  endwhile
                                endif
                                return (); // return (~ valueWasIn)
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
                                prev := head;
                                curr := prev->arr[1];
                                i := 1;
                                while (i >= 0) do
                                  curr := prev->arr[i];
                                  while (curr != null /\ curr->data < e) do
                                    prev := curr;
                                    curr := prev->arr[i];
                                  endwhile
                                  if (curr != null /\ curr->data != e) then
                                    removeFrom := i - 1;
                                  endif
                                  update[i] := prev;
                                  i := i - 1;
                                endwhile
                                valueWasIn := curr->data = e; // skip;
                                if (valueWasIn) then
                                  i := removeFrom;
                                  while (i >= 0) do
                                    update[i]->arr[i] := curr->arr[i]
                                    $ if (i=0) then
                                        region := region SetDiff {curr};
                                      endif
                                    $
                                    i := i - 1;
                                  endwhile
                                endif
                                return (); // return (valueWasIn)
                              end
                            
