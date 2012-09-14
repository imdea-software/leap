
global
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
  head->next[0] = tail /\
  tail->next[0] = null


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
                                addr cover
                                bool valueIsIn
                              begin
                                i := K - 1;
                                prev := head;
                                prev->lock[i];
                                curr := prev->next[i];
                                curr->lock[i];
                                while (0 <= i /\ curr->data != e) do
                                  if (i < K-1) then
                                    prev->lock[i];
                                    prev->unlock[i+1];
                                    if (i < K-2) then
                                      cover->unlock[i+2];
                                    endif
                                    cover := curr;
                                    curr := prev->next[i];
                                    curr->lock[i];
                                  endif
                                  while (curr->data < e) do
                                    prev->unlock[i];
                                    prev := curr;
                                    curr := prev->next[i];
                                    curr->lock[i];
                                  endwhile
                                  i := i -1;
                                endwhile
                                valueIsIn := (curr->data = e);
                                if (i = K-1) then
                                  curr->unlock[i];
                                  prev->unlock[i];
                                else
                                  if (i < K-2) then
                                    cover->unlock[i+2];
                                  endif
                                  curr->unlock[i+1];
                                  prev->unlock[i+1];
                                endif
                                return(); //return (valueIsIn)
                              end

// ----- INSERT ----------------------------------------------


                              procedure insert (e:elem)
                                addrarr update
                                addr prev
                                addr curr
                                addr newCell
                                addr cover
                                int lvl
                                int i
                                bool valueWasIn := false

                              begin
                                lvl := havocLevel();
                                prev := head;
                                prev->lock[K-1];
                                curr := prev->next[K-1];
                                curr->lock[K-1];
                                i := K-1;
                                while (0 <= i) do
                                  if (i < K-1) then
                                    prev->lock[i];
                                    if (i >= lvl) then
                                      prev->unlock[i+1];
                                    endif
                                    if (i < K-2 /\ i > lvl-2) then
                                      cover->unlock[i+2];
                                    endif
                                    cover := curr;
                                    curr := prev->next[i];
                                    curr->lock[i];
                                  endif
                                  while (curr->data < e) do
                                    prev->unlock[i];
                                    prev := curr;
                                    curr := prev->next[i];
                                    curr->lock[i];
                                  endwhile
                                  update[i] := prev;
                                  i := i - 1;
                                endwhile
                                if (i < K-2) then
                                  cover->unlock[i+2];
                                endif
                                valueWasIn := (curr->data = e);
                                if (valueWasIs) then
                                  i := lvl;
                                  while (i >= 0) do
                                    update[i]->next[i]->unlock[i];
                                    update[i]->unlock[i];
                                    i := i - 1;
                                  endwhile
                                else
                                  newCell := mallocSL(e, lvl);
                                  i := 0;
                                  while (i <= lvl) do
                                    newCell->next[i] := update[i]->next[i];
                                    update[i]->next[i] := newCell;
                                    newCell->next[i]->unlock[i];
                                    update[i]->unlock[i];
                                    i := i + 1;
                                  endwhile
                                endif
                                return (); // return (~ valueWasIn);
                              end

// ----- REMOVE ----------------------------------------------


                              procedure remove (e:elem)
                                addrarr update
                                addr prev
                                addr curr
                                addr newCell
                                addr cover
                                int i
                                int deleteFrom
                                bool valueWasIn := false

                              begin
                                prev := head;
                                prev->lock[K-1];
                                curr := prev->next[K-1];
                                curr->lock[K-1];
                                cover := tail;
                                deleteFrom := K-1;
                                i := K-1;
                                while (0 <= i) do
                                  if (i < K-1) then
                                    prev->lock[i];
                                    if (prev->next[i+1]->data != e) then
                                      deleteFrom := i;
                                      prev->unlock[i+1];
                                    endif
                                    if (i < K-2 /\ cover->data !=e) then
                                      cover->unlock[i+2];
                                    endif
                                    cover := curr;
                                    curr := prev->next[i];
                                    curr->lock[i];
                                  endif
                                  while (curr->data < e) do
                                    prev->unlock[i];
                                    prev := curr;
                                    curr := prev->next[i];
                                    curr->lock[i];
                                  endwhile
                                  update[i] := prev;
                                  i := i - 1;
                                endwhile
                                if (i < K-2) then
                                  cover->unlock[i+2];
                                endif
                                valueWasIn := (curr->data = e);
                                i := deleteFrom;
                                while (i >= 0) do
                                  if (update[i]->next[i] = curr /\ curr->data = e) then
                                    update[i]->next[i] := curr->next[i];
                                    curr->unlock[i];
                                  else
                                    update[i]->next[i]->unlock[i];
                                  endif
                                  update[i]->unlock[i];
                                  i := i - 1;
                                endwhile
                                return (); // return (valueWasIn);
                              end
                            
