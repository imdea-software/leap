
global
  lockarr locks
  int locksLength
  int capacity
  bucketarr table

  ghost addrSet region
  ghost elemSet elements

assume
  region = {null} /\
  elements = eempty /\

  hashmap(heap, region, elements, table, capacity)


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
                                    call contains(e);
                                  _or_
                                    call add(e);
                                  endchoice
                                endwhile
                                return ();
:main_e]
:main_body]
                              end


// ----- HASH FUNCTION ---------------------------------------

                            procedure hash (e:elem) : int
                              int code
                            begin
                              code := hashCode(e);
                              return (code);
                            end

// ----- HASHMAP CONTAINS ------------------------------------

                            procedure contains (e:elem) : bool
                              int hashId
                              int myBucket
                              int myLock
                              bool result
                            begin
                              hashId := call hash(e);
                              myBucket := hashId % capacity;
                              result := call search(table[myBucket].binit, e);
                              return(result);
                            end

// ----- HASHMAP ADD -----------------------------------------

                            procedure add (e:elem)
                              int hashId
                              int myBucket
                              int myLock
                              addr prev
                              addr curr
                              addr node
                            begin
                              hashId := call hash(e);
                              myLock := hashId % locksLength;
:myLock_set[
                              locks[myLock] := lock(locks[myLock],me);
:locked_bucket[
                              myBucket := hashId % capacity;
:myBucket_set[

                              curr := table[myBucket].binit;
                              while (curr->data != e /\ curr != null) do
                                curr := curr->next;
                              endwhile
                              if (curr = null) then
                                node := malloc(e, table[myBucket].binit, #);
:adding_node
                                table[myBucket] := mkbucket(node,
                                                            table[myBucket].bend,
                                                            union(table[myBucket].bregion, {node}),
                                                            table[myBucket].btid)
                                  $
                                    elements := eunion (elements, esingle(e));
                                    region := union (region, {node});
                                  $
                              endif
                              locks[myLock] := unlock(locks[myLock]);
:locked_bucket]
:myBucket_set]
:myLock_set]
                            end


// ----- HASHMAP RESIZE --------------------------------------

                            procedure resize ()
                              int newCapacity
                              int oldCapacity
                              int hashId
                              int i
                              bucket b
                              elem e
                              addr itr
                              bucketarr oldTable
                            begin
                              i := 0;
                              while (i < locksLength) do
                                locks[i] := lock(locks[i], me);
                              endwhile
                              oldCapacity := capacity;
                              if (oldCapacity != capacity) then
                                i := 0;
                                while (i < locksLength) do
                                  locks[i] := unlock(locks[i]);
                                endwhile
                                return ();
                              endif
                              newCapacity := 2 * oldCapacity;
                              oldTable := table;
                              i := 0;
                              while (i < newCapacity) do
                                table[i] := mkbucket (null, null, empty, #);
                              endwhile
                              capacity := newCapacity;
                              i := 0;
                              while (i < oldCapacity) do
                                b := oldTable[i];
                                itr := b.binit;
                                while (itr != null) do
                                  e := itr -> data;
                                  call add(itr -> data);
                                  itr := itr -> next;
                                endwhile
                                i := i + 1;
                              endwhile
                              i := 0;
                              while (i < locksLength) do
                                locks[i] := unlock(locks[i]);
                              endwhile
                              return ();
                            end




// ----- LIST SEARCH ----------------------------------------------

                              procedure search (head:addr, e:elem) : bool
                                addr curr
                                bool result
                              begin
                                curr := head;
                                while (curr->data != e /\ curr != null) do
                                  curr := curr->next;
                                endwhile
                                result := curr->data = e;
                                return (result);
                              end


