
global
  addr head
  addr tail
  ghost addrSet region
  ghost elemSet elements
  ghost elemSet enqueuSet
  ghost elemSet dequeueSet

assume
  region = union ({head}, {null}) /\
  head = tail /\
  head != null /\
  head->next = null /\
  enqueuSet = eempty /\
  dequeueSet = eempty


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
:enqueue_last_was_tail[
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
                                          region := union (region, {n});
                                          enqueuSet := eunion (enqueuSet, esingle (e));
                                        endif$
:not_compared]
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
:enqueue_next_not_null
                                      {
                                        if (tail = last) then
                                          tail := nextptr;
                                        endif
                                      }
                                    endif
                                  endif
:next_follows_last]
:enqueue_last_was_tail]
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
:dequeue_first_was_head[
                                  last := tail;
:dequeue_last_was_tail[
                                  nextptr := first->next;
:next_follows_first[
                                  if (first = head) then
                                    if (first = last) then
:first_is_last[
                                      if (nextptr = null) then
                                        return (lowestElem);
                                      endif
:dequeue_next_not_null
                                      {
                                        if (tail = last) then
                                          tail := nextptr;
                                        endif
                                      }
:first_is_last]
                                    else
:first_not_last[
                                      value := nextptr->data;
:value_assigned
                                      {
                                        if (head = first) then
                                          head := nextptr;
                                          comparison := true;
                                        endif
                                      }
                                      $ if (head = first) then
                                          region := diff (region, {first});
                                          dequeueSet := eunion (dequeueSet, esingle(value));
                                        endif$
:first_not_last]
                                      if (comparison) then
                                        return (value);
                                      endif
                                    endif
                                  endif
:next_follows_first]
                                endwhile
:dequeue_first_was_head]
:dequeue_last_was_tail]
                                skip;
                              end
                            
