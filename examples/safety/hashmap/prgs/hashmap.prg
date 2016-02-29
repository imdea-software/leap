
global
  lockarr locks
  int locksLength
  int capacity
  bucketarr table

	ghost addrSet region
  ghost elemSet elements

assume
	region = {null} /\
	elements = eempty


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
                              addr newAddr
                              bucket b
                            begin
                              hashId := call hash(e);
                              myLock := hashId % locksLength;
                              locks[myLock] := lock(locks[myLock],me);
                              myBucket := hashId % capacity;
                              newAddr := call insert(table[myBucket].binit, e);
                              table[myBucket].binit := newAddr;
                              locks[myLock] := unlock(locks[myLock]);
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

// ----- LIST INSERT ----------------------------------------------


                              procedure insert (head:addr, e:elem) : addr
                                addr curr
                                addr node
                              begin
                                curr := head;
                                while (curr->data != e /\ curr != null) do
                                  curr := curr->next;
                                endwhile
                                if (curr = null) then
                                  node := malloc(e, head, #);
                                else
                                  node := curr;
                                endif
                                return (node);
                              end

