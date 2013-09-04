
global
  addr head
  addr tail
  ghost addrSet region

assume
  region = {head} Union {tail} Union {null} /\
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
                                  choice
                                    call search(e);
                                  _or_
                                    call insert(e);
                                  _or_
                                    call remove(e);
                                  endchoice
                                endwhile
                                return ();
:main_body]
                              end

// ----- SEARCH ----------------------------------------------


                              procedure search (e:elem)
                                addr prev
                                addr curr
                                addr aux

                              begin
                                prev := head;
                                prev->lock;
                                curr := prev->next;
                                curr->lock;

                                while (curr->data != e) do
                                  aux := prev;
                                  prev := curr;
                                  aux->unlock;
                                  curr := curr->next;
                                  curr->lock;
                                endwhile

                                prev->unlock;
                                curr->unlock;
                                return ();
                              end

// ----- INSERT ----------------------------------------------


                              procedure insert (e:elem)
                                addr prev
                                addr curr
                                addr aux

                              begin
:ins_head_next_diff[
                                prev := head;
:ins_prev_def[
:ins_prev_is_head[
                                prev->lock;
:ins_owns_prev[
                                curr := prev->next;
:ins_head_next_diff]
:ins_curr_def[
:ins_follows[
                                curr->lock;
:ins_prev_is_head]
:ins_owns_curr_one[

                                while (curr != null /\ curr->data != e) do
:ins_while[
                                  aux := prev;
:ins_aux_eq_prev
                                  prev := curr;
:ins_equals[
:ins_aux_before_prev
                                  aux->unlock;
                                  curr := curr->next;
:ins_equals]
:ins_while]
:ins_owns_curr_one]
                                  curr->lock;
:ins_owns_curr_two[
                                endwhile


                                if (curr->data != e) then
                                  aux := malloc(e, null, #);
:after_malloc[
                                  aux->next := curr;
:ins_aux_before_curr
:ins_diff[
                                  prev->next := aux
                                    $region := region Union {aux}; $
:ins_follows]
:after_malloc]
                                endif
                                prev->unlock;
:ins_owns_prev]
:ins_prev_def]
                                curr->unlock;
:ins_owns_curr_two]
:ins_curr_def]
:ins_diff]
                                return();
                                
                              end

// ----- REMOVE ----------------------------------------------


                              procedure remove (e:elem)
                                addr prev
                                addr curr
                                addr aux

                              begin
:rem_head_next_diff[
                                prev := head;
:rem_prev_def[
:rem_prev_is_head[
                                prev->lock;
:rem_owns_prev[
                                curr := prev->next;
:rem_head_next_diff]
:rem_curr_def[
:rem_follows[
                                curr->lock;
:rem_prev_is_head]
:rem_owns_curr_one[
                                while (curr != tail /\ curr->data != e) do
:rem_while[
                                  aux := prev;
:rem_aux_eq_prev
                                  prev := curr;
:rem_equals[
:rem_aux_before_prev
                                  aux->unlock;
                                  curr := curr->next;
:rem_equals]
:rem_while]
:rem_owns_curr_one]
                                  curr->lock;
:rem_owns_curr_two[
                                endwhile
                                if (curr != tail /\ curr->data = e) then
:rem_if_one
                                  aux := curr->next;
:rem_if_two
                                  prev->next := aux
                                    $ region := region SetDiff {curr}; $
:rem_follows]
:rem_curr_def]
                                endif
:rem_diff[
                                prev->unlock;
:rem_owns_prev]
:rem_prev_def]
                                curr->unlock;
:rem_diff]
:rem_owns_curr_two]
                                return();
                              end
                            
