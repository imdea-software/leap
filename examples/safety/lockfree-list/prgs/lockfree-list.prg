
global
  addr head
  addr tail
  ghost addrSet region
  ghost elemSet elements

assume
  region = union(union({head},{tail}),{null}) /\
  elements = eunion (esingle (rd(heap,head).data),
                     esingle (rd(heap,tail).data)) /\
  rd(heap, head).data = lowestElem /\
  rd(heap, tail).data = highestElem /\
  head != tail /\
  head != null /\
  tail != null /\
  head->next = tail /\
  tail->next = null


// ----- PROGRAM BEGINS --------------------------------------
                            
                              procedure main ()
                                elem e
                              begin
:main_body[
                                while (true) do
                                  // Generate random e
                                  e := havocListElem();
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



                              procedure search (e:elem) : bool
                                mark curr_mark
                                addr curr
                                addr succ
                                bool result
                              begin
                                curr := head;
                                while (curr->data < e) do
                                  curr := curr->next;
                                  {
                                    succ := curr->next;
                                    curr_mark := curr->next->marked;
                                  }
                                endwhile
                                result := curr->data = e /\ curr_mark = F;
                                return (result);
                              end


// ----- INSERT ----------------------------------------------


                              procedure insert (e:elem)
                                addr prev := null
                                addr curr := null
                                addr succ := null
                                addr n
                                mark curr_mark
                                bool snip := true
                                bool comparison := false
                              begin
                                while(true) do
                                  prev := head;
                                  curr := prev->next;
                                  while(snip) do
                                    {
                                      succ := curr->next;
                                      curr_mark := curr->next->marked;
                                    }
                                    while ((snip) /\ curr_mark = T) do
                                      {
                                        if (prev->next = curr /\ prev->next->marked = F) then
                                          prev->next := succ;
                                          snip := true;
                                        endif
                                      }
                                      if (snip) then
                                        curr := succ;
                                        succ := curr->next;
                                        curr_mark := curr->next->marked;
                                      endif
                                    endwhile
                                    if (curr->data > e \/ curr->data = e) then
                                      if (curr->data = e) then
                                        return ();
                                      else
                                        n := malloc(e, null, #);
                                        {
                                          n->next := curr;
                                          n->marked := F;
                                        }
                                        {
                                          if (prev->next = curr /\ prev->next->marked = F) then
                                            prev->next := curr;
                                            comparison := true;
                                          endif
                                        }
                                        if (comparison) then
                                          return ();
                                        endif
                                      endif
                                    endif
                                  endwhile
                                endwhile
                              end

// ----- REMOVE ----------------------------------------------


                              procedure remove (e:elem)
                                addr prev := null
                                addr curr := null
                                addr succ := null
                                mark curr_mark
                                bool snip := true

                              begin
                                while(true) do
                                  prev := head;
                                  curr := prev->next;
                                  while(snip) do
                                    {
                                      succ := curr->next;
                                      curr_mark := curr->next->marked;
                                    }
                                    while ((snip) /\ curr_mark = T) do
                                      {
                                        if (prev->next = curr /\ prev->next->marked = F) then
                                          prev->next := succ;
                                          snip := true;
                                        endif
                                      }
                                      if (snip) then
                                        curr := succ;
                                        succ := curr->next;
                                        curr_mark := curr->next->marked;
                                      endif
                                    endwhile
                                    if (curr->data > e \/ curr->data = e) then
                                      if (curr->data = e) then
                                        return ();
                                      else
                                        succ := curr->next;
                                        {
                                          if (curr->next = succ) then
                                            snip := true;
                                          else
                                            snip := false;
                                          endif
                                        }
                                        if (snip) then
                                          {
                                            if (prev->next = curr /\ prev->next->marked = F) then
                                              prev->next := succ;
                                            endif
                                          }
                                          return();
                                        endif
                                      endif
                                    endif
                                  endwhile
                                endwhile
                              end
