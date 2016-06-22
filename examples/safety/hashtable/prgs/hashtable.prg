
global
  lockarr locks
  bucketarr table
  int locksLen
  int capacity

  ghost addrSet region
  ghost elemSet elements

assume
  region = {null} /\
  elements = eempty /\

  hashtbl(heap, region, elements, table, capacity)


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
                                    call add(e, table);
                                  _or_
                                    call resize();
                                  endchoice
                                endwhile
                                return ();
:main_e]
:main_body]
                              end



// ----- HASHMAP CONTAINS ------------------------------------

                            procedure contains (e:elem) : bool
                              int hashId
                              int myLock
                              bool result
                            begin
                              hashId := hashCode(e);
                              myLock := hashId % locksLen;
                              locks[myLock] := lock(locks[myLock], me);
                              result := call search(table[hashId % capacity].binit, e);
                              locks[myLock] := unlock(locks[myLock]);
                              return(result);
                            end

// ----- HASHMAP ADD -----------------------------------------

                            procedure add (e:elem, tbl:bucketarr)
                              int hashId
                              int myLock
                              int myBucket
                              addr prev
                              addr curr
                              addr node
                            begin
:procedure_add[
                              hashId := hashCode(e);
                              myLock := hashId % locksLen;
:add_lock_computed[
                              locks[myLock] := lock(locks[myLock],me);
:add_own_lock[
                              myBucket := hashId % capacity;
                              curr := tbl[myBucket].binit;
                              while (curr->data != e /\ curr != null) do
                                curr := curr->next;
                              endwhile
                              if (curr = null) then
                                node := malloc(e, tbl[myBucket].binit, #);
                                tbl[myBucket] := mkbucket(node,
                                                          tbl[myBucket].bend,
                                                          union(tbl[myBucket].bregion, {node}),
                                                          #)
                                  $
                                    elements := eunion (elements, esingle(e));
                                    region := union (region, {node});
                                  $
                              endif
                              locks[myLock] := unlock(locks[myLock]);
:add_own_lock]
:add_lock_computed]
:procedure_add]
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
                              bucketarr newTable
                              addrSet newRegion
                              elemSet newElements
                            begin
                              oldCapacity := capacity;
                              i := 0;
                              while (i < locksLen) do
                                locks[i] := lock(locks[i], me);
                                i := i + 1;
                              endwhile
                              if (oldCapacity != capacity) then
                                i := 0;
                                while (i < locksLen) do
                                  locks[i] := unlock(locks[i]);
                                  i := i - 1;
                                endwhile
                                return ();
                              endif

:resize_own_all_locks[
                              newCapacity := 2 * oldCapacity;

                              i := 0;
                              while (i < newCapacity) do
                                newTable[i] := mkbucket (null, null, empty, #);
                                i := i + 1;
                              endwhile

:newTable_init[
                              i := 0;
                              while (i < oldCapacity) do
                                b := table[i];
                                itr := b.binit;
                                while (itr != null) do
                                  call add(itr -> data, newTable);
                                  itr := itr -> next;
                                endwhile
                                i := i + 1;
                              endwhile

                              table := newTable;
                              capacity := newCapacity;
:newTable_init]
:resize_own_all_locks]
                              i := 0;
                              while (i < locksLen) do
                                locks[i] := unlock(locks[i]);
                                i := i + 1;
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


