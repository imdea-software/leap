
global
    int maxLevel
    addr head
    addr tail
    ghost addrSet region
    int K := 3

//  addr head
//  addr tail
//  ghost addrSet region
//  ghost elemSet elements

assume
  region = {head} Union {tail} Union {null} /\
//  elements = UnionElem (
//              UnionElem (SingleElem (rd(heap,head).data),
//                         SingleElem (rd(heap,tail).data)),
//                         SingleElem (rd(heap,null).data)) /\
//  // or orderlist (heap, head, null)
  rd(heap, head).data = lowestElem /\
  rd(heap, tail).data = highestElem /\
  head != tail /\
  head != null /\
  tail != null /\
  head->arr[0] = tail /\
  tail->arr[0] = null


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
                                i := K - 1;
                                prev := head;
                                prev->lock[i];
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
                                lvl := havocLevel();
                                if (lvl > maxLevel) then
                                  i := maxLevel + 1;
                                  while (i <= lvl) do
                                    head->arr[i] := tail;
                                    tail->arr[i] := null;
                                    i := i + 1;
                                  endwhile
                                endif
                                prev := head;
                                curr := prev->arr[maxLevel];
                                i := maxLevel;
                                while (0 <= i /\ ~(valueWasIn)) do
                                  curr := prev->arr[i];
                                  while (curr->data < e) do
                                    prev := curr;
                                    curr := prev->arr[i];
                                  endwhile
                                  update[i] := prev;
                                  i := i - 1;
                                  valueWasIn := (curr->data = e);
                                endwhile
                                if (~ (valueWasIn)) then
                                  newCell := mallocSL(e,lvl);
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
                                int removeFrom := maxLevel
                                int i
                                addr prev
                                addr curr
                                bool valueWasIn
                              begin
                                prev := head;
                                curr := prev->arr[maxLevel];
                                i := maxLevel;
                                while (i >= 0) do
                                  curr := prev->arr[i];
                                  while (curr->data < e) do
                                    prev := curr;
                                    curr := prev->arr[i];
                                  endwhile
                                  if (curr->data != e) then
                                    removeFrom := i - 1;
                                  endif
                                  update[i] := prev;
                                  i := i - 1;
                                endwhile
                                valueWasIn := curr->data = e;
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
                            
