
global
  addr top
//  addr tail
  ghost addrSet region
  ghost elemSet elements
  ghost elemSet pushSet
  ghost elemSet popSet

assume
  region = {null} /\
  top = null /\
//  head = tail /\
//  head != null /\
//  head->next = null /\
  pushSet = eempty /\
  popSet = eempty


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
                                    call push(e);
                                  _or_
                                    call pop();
                                  endchoice
                                endwhile
                                return ();
:main_e]
:main_body]
                              end


// ----- PUSH ------------------------------------------------

 


                              procedure push (e:elem)
                                addr n
                                addr oldTop
                                bool comparison := false
                              begin
                                n := malloc(e, null, #);
:n_created[
:n_disconnected[
                                while (true) do
                                  oldTop := top;
:push_oldTop_set[
                                  n->next := oldTop;
:connecting
                                  {
                                    if (top = oldTop) then
                                      top := n;
                                      comparison := true;
                                    endif
                                  }
                                  $
                                    if (top = oldTop) then
                                      region := union (region, {n});
                                      pushSet := eunion (pushSet, esingle(e));
                                    endif
                                  $
:n_disconnected]
:push_compare
                                  if (comparison) then
                                    return();
                                  endif
:push_oldTop_set]
                                endwhile
:n_created]
                                return();
                              end


// ----- REMOVE ----------------------------------------------


                              
                              procedure pop () : elem
                                addr oldTop
                                addr newTop
                                elem value
                                bool comparison := false
                              begin
                                while (true) do
                                  oldTop := top;
:pop_oldTop_set[
                                  if (oldTop = null) then
                                    return (lowestElem);
                                  endif
:oldTop_not_null[
                                  newTop := oldTop->next;
:newTop_follows_oldTop[
                                  value := oldTop->data;
:pop_removing
                                  {
                                    if (top = oldTop) then
                                      top := newTop;
                                      comparison := true;
                                    endif
                                  }
                                  $
                                    if (top = oldTop) then
                                      region := diff (region, {oldTop});
                                      popSet := eunion (popSet, esingle (value));
                                    endif
                                  $
:newTop_follows_oldTop]
                                  if (comparison) then
                                    return (value);
                                  endif
:oldTop_not_null]
:pop_oldTop_set]
                                endwhile
                                skip;
                              end

                            
