global
	int maxLevel
	addr head
	ghost addrSet region
	ghost elemSet elements

assume
	region = {head} Union {null} /\
	elements = SingleElem (lowestElem) /\
	skiplist(heap, region, 0, head, null, elements) /\
  rd(heap, head).data = lowestElem /\
	head != null /\
	head->arr[0] = null /\
	maxLevel = 0


// ----- PROGRAM BEGINS --------------------------------------
                            
                              procedure main ()
                                elem e
                              begin
:main_body[
                                while (true) do
                                  // Generate random e
                                  e := havocSLElem();
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




															procedure search (value:elem) : bool
																	int i
																	addr element
																	addr nextElement
																	bool found

															begin
																	element := head;

																	i := maxLevel;
																	while (i >= 0) do
																		nextElement := element->arr[i];
																		while ( (nextElement != null) /\ (~ (nextElement->data > value)) ) do
																			element := nextElement;
																			nextElement := element->arr[i];
																		endwhile
																		i := i - 1;
																	endwhile

																	// now nextElement is > value
																	// element is <= , make it >
																	//
																	element := nextElement;
																	found := (element->data = value);
																	return (found);
															end


															procedure insert(value:elem)
																int i
																int newLevel
																addr element
																addr nextElement
																addrarr update

															begin
																// scan all levels while key < value
																// starting with header in his level
																element := head;
																i := maxLevel;
																while (i >= 0) do
																	nextElement := element->arr[i];
																	while( (nextElement != null) /\ (nextElement->data < value) ) do
																		element := nextElement;
																		nextElement := element->arr[i];
																	endwhile
																	update[i] := element;
																	i := i - 1;
																endwhile

																// key is < value
																element := element->arr[0];

																if ( (element = null) \/ (element->data != value) ) then
																	// new key. add to list
																	// get new level and fix list level

																	// get new level
																	newLevel := havocLevel();
																	if (newLevel > maxLevel) then
																		// adjust header level
																		i := maxLevel + 1;
																		while (i <= newLevel) do
																			update[i] := head;
																			i := i + 1;
																		endwhile
																		maxLevel := newLevel;
																	endif

																	// make new element [NEW *******]
																	element := mallocSL (value, newLevel);
																	i := 0;
																	while (i <= newLevel) do
																		element->arr[i] := update[i]->arr[i];
																		update[i]->arr[i] := element
																			$ if (i=0) then
																					region := region Union {element};
																					elements := UnionElem (elements, SingleElem(value));
																				endif
																			$
																		i := i + 1;
																	endwhile
																endif
																return();
															end


															procedure remove (value:elem)
																int i
																addr element
																addr nextElement
																addrarr update

															begin
																// scan all levels while key < value
																// starting with header in his level
																element := head;
																i := maxLevel;
																while (i >= 0 ) do
																	nextElement := element->arr[i];
																	while ( (nextElement != null) /\ (nextElement->data < value) ) do
																		element := nextElement;
																		nextElement := element->arr[i];
																	endwhile
																	update[i] := element;
																	i := i - 1;
																endwhile

																// key is < value
																element := element->arr[0];

																// if key exists
																if( (element != null) /\ (element->data = value) ) then
																	i := 0;
																	while (i <= maxLevel) do
																		if (update[i]->arr[i] = element) then
																			update[i]->arr[i] := element->arr[i]
																			$ if (i=0) then
																					region := region SetDiff {element};
																					elements := SetDiffElem (elements, SingleElem(value));
																				endif
																			$
																		endif
																		i := i + 1;
																	endwhile

																	// set new header level
																	while ( (maxLevel > 0) /\ (head->arr[maxLevel] = null) ) do
																		maxLevel := maxLevel - 1;
																	endwhile
																endif
															end

