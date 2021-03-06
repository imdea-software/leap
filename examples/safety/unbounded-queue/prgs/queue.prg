
global
  addr head
  addr tail
  ghost addrSet region
  ghost elemSet elements
  cell queueLock
  ghost elemSet enqueuSet
  ghost elemSet dequeueSet

assume
  region = union ({head}, {null}) /\
  head = tail /\
  head != null /\
  head->next = null /\
  queueLock.lockid = # /\
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

                              begin
                                queueLock := queueLock.lock;
:locked_enqueue[
                                n := malloc(e, null, #);
:n_not_null[
                                tail->next := n
                                $
                                  region := union (region, {n});
                                  enqueuSet := eunion (enqueuSet, esingle(e));
                                $
:tail_next_n
                                tail := n;
:n_not_null]
                                queueLock := queueLock.unlock;
:locked_enqueue]
                                return();
                              end

// ----- REMOVE ----------------------------------------------


                              procedure dequeue () : elem
                                elem result

                              begin
                                queueLock := queueLock.lock;
:locked_dequeue_one[
                                if (head->next = null) then
                                  queueLock := queueLock.unlock;
:locked_dequeue_one]
                                  return (lowestElem);
                                else
:locked_dequeue_two[
:head_next_not_null[
                                  result := head->next->data;
:dequeue_point
                                  head := head->next
                                    $
                                      region := diff(region, {head});
                                      dequeueSet := eunion (dequeueSet, esingle(result));
                                    $
:head_next_not_null]
                                endif
                                queueLock := queueLock.unlock;
:locked_dequeue_two]
:dequeue_result
                                return (result);
                              end
                            
