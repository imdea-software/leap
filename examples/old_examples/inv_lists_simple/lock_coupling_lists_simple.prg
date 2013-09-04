
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



                              procedure insert (e:elem)
                                addr prev
                                addr curr
                                addr aux

                              begin
:head_next_diff[
                                prev := head;
:prev_def[
:prev_is_head[
                                prev->lock;
:owns_prev_one[
:prev_next_diff
                                curr := prev->next;
:head_next_diff]
:curr_def[
:follows[
                                curr->lock;
:prev_is_head]
:owns_curr_one[

                                while (curr != null /\ curr->data != e) do
:inside_while[
                                  prev->unlock;
:owns_prev_one]
                                  prev := curr;
:owns_prev_two[
:equals
                                  curr := curr->next;
:inside_while]
:owns_curr_one]
                                  curr->lock;
:owns_curr_two[
                                endwhile

                                if (curr->data != e) then
                                  aux := malloc(e, null, #);
:after_malloc_one
:after_new[
                                  aux->next := curr;
:follows]
:after_malloc_two
:diff[
                                  prev->next := aux
                                    $region := region Union {aux}; $
:after_new]
                                endif
:after_if
                                prev->unlock;
:owns_prev_two]
                                curr->unlock;
:owns_curr_two]
:curr_def]
:prev_def]
:diff]
                              end
