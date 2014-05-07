
global
  addr head
  addr tail
  ghost addrSet region
  ghost elemSet elements
  ghost elemSet enqueuSet
  ghost elemSet dequeueSet

assume
  region = {head} Union {null} /\
  head = tail /\
  head != null /\
  head->next = null /\
  enqueuSet = EmptySetElem /\
  dequeueSet = EmptySetElem


// ----- PROGRAM BEGINS --------------------------------------
                            
                              procedure main ()
                                elem e
                              begin
:main_body[
                                while (true) do
:main_e[
                                  choice
                                  // Generate random e
                                  e := havocListElem();
                                    call enqueue(e);
                                  _or_
                                    call dequeue();
                                  endchoice
                                endwhile
                                return ();
:main_e]
:main_body]
                              end


// ----- PUSH ------------------------------------------------

 


                              procedure enqueue (e:elem)
                                addr n
                                addr last
                                addr nextptr
                                bool comparison := false

                              begin
:not_compared[
                                n := malloc(e, null, #);
:n_created[
:n_disconnected[
                                while (true) do
                                  last := tail;
:last_was_tail[
                                  nextptr := last->next;
:next_follows_last[
                                  if (last = tail) then
                                    if (nextptr = null) then
:nextptr_is_null[
                                      {
                                        if (last->next = nextptr) then
                                          last->next := n;
                                          comparison := true;
                                        endif
                                      }
                                      $ if (last->next = nextptr) then
                                          region := region Union {n};
                                        endif$
:not_compared]
:next_follows_last]
:n_disconnected]
:comparison_done[
                                      if (comparison) then
:comparison_holds
                                        {
                                          if (tail = last) then
                                            tail := n;
                                          endif
                                        }
                                        return ();
                                      endif
:comparison_done]
:nextptr_is_null]
                                    else
:next_not_null
                                      {
                                        if (tail = last) then
                                          tail := nextptr;
                                        endif
                                      }
                                    endif
:last_was_tail]
                                  endif
                                endwhile
:n_created]
                                return();
                              end

// ----- REMOVE ----------------------------------------------


                              procedure dequeue () : elem
                                elem value
                                addr first
                                addr last
                                addr nextptr
                                bool comparison := false

                              begin
                                while (true) do
                                  first := head;
                                  last := tail;
                                  nextptr := first->next;
                                  if (first = head) then
                                    if (first = last) then
                                      if (nextptr = null) then
                                        return (lowestElem);
                                      endif
                                      {
                                        if (tail = last) then
                                          tail := nextptr;
                                        endif
                                      }
                                    else
                                      value := nextptr->data;
                                      {
                                        if (head = first) then
                                          head := nextptr;
                                          comparison := true;
                                        endif
                                      }
                                      if (comparison) then
                                        return (value);
                                      endif
                                    endif
                                  endif
                                endwhile
                              end
                            
