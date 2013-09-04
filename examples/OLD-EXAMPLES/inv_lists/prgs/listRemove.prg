
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


                              procedure main ()
                              begin
                              end


                              procedure remove (e:elem)
                                addr prev
                                addr curr
                                addr aux

                              begin
:head_next_diff_rem[
                                prev := head;
:prev_def_rem[
:prev_is_head_rem[
                                prev->lock;
:owns_prev_rem[
:prev_next_diff_rem
                                curr := prev->next;
:head_next_diff_rem]
:curr_def_rem[
:follows_rem[
                                curr->lock;
:prev_is_head_rem]
:owns_curr_rem_one[
:begin_while_rem
                                while (curr != tail /\ curr->data != e) do
:inside_while_rem[
                                  aux := prev;
:equals_aux_prev
                                  prev := curr;
:equals_rem[
                                  aux->unlock;
                                  curr := curr->next;
:equals_rem]
:inside_while_rem]
:owns_curr_rem_one]
                                  curr->lock;
:owns_curr_rem_two[
                                endwhile
:after_while_rem[
                                if (curr != tail /\ curr->data = e) then
:inside_if_one
                                  aux := curr->next;
:inside_if_two
                                  prev->next := aux
                                    $ region := region SetDiff {curr}; $
:follows_rem]
:curr_def_rem]
                                endif
:diff_rem[
:curr_maybe_def_rem[
                                prev->unlock;
:owns_prev_rem]
:prev_def_rem]
                                curr->unlock;
:diff_rem]
:after_while_rem]
:owns_curr_rem_two]
:curr_maybe_def_rem]
                              end
                            
