
global
  addr head
  addr tail
  ghost addrSet region
  ghost elemSet elements
  ghost elemSet enqueuSet
  ghost elemSet dequeueSet

assume
  region = {head} Union {null} /\
//  elements = SingleElem (rd(heap,head).data) /\
  // or orderlist (heap, head, null)
//  rd(heap, head).data = lowestElem /\
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
                                n := malloc(e, null, #);
                                while (true) do
                                  last := tail;
                                  nextptr := last->next;
                                  if (last = tail) then
                                    if (nextptr = null) then
                                      {
                                        if (last->next = nextptr) then
                                          last->next := n;
                                          comparison := true;
                                        endif
                                      }
                                      if (comparison) then
                                        {
                                          if (tail = last) then
                                            tail := n;
                                          endif
                                        }
                                        return ();
                                      endif
                                    else
                                      {
                                        if (tail = last) then
                                          tail := nextptr;
                                        endif
                                      }
                                    endif
                                  endif
                                endwhile
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
                            
