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
//                                  _or_
//																		call remove(e);
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
:insert_body[
																// scan all levels while key < value
																// starting with header in his level
																element := head;
:insert_element_is_head[
:insert_element_in_region[
																i := maxLevel;
:insert_element_is_head]
:insert_lookup_loop[
:insert_element_next_region_one[
:testing_one
																while (i >= 0) do
																	nextElement := element->arr[i];
:insert_element_next_region_one]
:insert_nextElement_in_region[
:insert_element_nextElement_one[
																	while( (nextElement != null) /\ (nextElement->data < value) ) do
:insert_nextElement_low
																		element := nextElement;
:insert_element_nextElement_one]
:insert_element_is_nextElement
																		nextElement := element->arr[i];
																	endwhile
:insert_nextElement_in_region]
:insert_element_nextElement_two[
																	update[i] := element;
:insert_update_set
																	i := i - 1;
:insert_element_nextElement_two]
																endwhile
:insert_lookup_loop]
:insert_element_in_region]

:insert_update_all_set[
:insert_test_update_zero
																// key is < value
																element := element->arr[0];

:insert_final_if_condition
																if ( (element = null) \/ (element->data != value) ) then
																	// new key. add to list
																	// get new level and fix list level

:insert_update_all_order[
																	// get new level
																	newLevel := havocLevel();
																	if (newLevel > maxLevel) then
																		// adjust header level
																		i := maxLevel + 1;
:insert_increasing_level[
																		while (i <= newLevel) do
																			update[i] := head;
:insert_update_i_head
																			update[i]->arr[i] := null;
:insert_increment_i
																			i := i + 1;
:insert_increasing_level]
																		endwhile
:insert_new_levels_filled
																		maxLevel := newLevel;
																	endif

																	// make new element [NEW *******]
:insert_newLevel_bounded[
																	element := mallocSL (value, newLevel);
:insert_newCell_created[
:insert_i_set_zero
																	i := 0;
:insert_update_all_order]
:insert_newCell_low_connected[
:insert_newCell_unconnected[
																	while (i <= newLevel) do
:insert_not_all_processed[
																		element->arr[i] := update[i]->arr[i];
:insert_element_next_connected
																		update[i]->arr[i] := element
																			$ if (i=0) then
																					region := region Union {element};
																					elements := UnionElem (elements, SingleElem(value));
																				endif
																			$
:insert_not_all_processed]
:insert_newCell_unconnected]
:insert_i_increases
																		i := i + 1;
																	endwhile
:insert_newCell_created]
:insert_newCell_low_connected]
:insert_newLevel_bounded]
:insert_update_all_set]
																endif
																return();
:insert_body]
															end


//															procedure remove (value:elem)
//																int i
//																addr element
//																addr nextElement
//																addrarr update
//
//															begin
//																// scan all levels while key < value
//																// starting with header in his level
//																element := head;
//																i := maxLevel;
//																while (i >= 0 ) do
//																	nextElement := element->arr[i];
//																	while ( (nextElement != null) /\ (nextElement->data < value) ) do
//																		element := nextElement;
//																		nextElement := element->arr[i];
//																	endwhile
//																	update[i] := element;
//																	i := i - 1;
//																endwhile
//
//																// key is < value
//																element := element->arr[0];
//
//																// if key exists
//																if( (element != null) /\ (element->data = value) ) then
//																	i := 0;
//																	while (i <= maxLevel) do
//																		if (update[i]->arr[i] = element) then
//																			update[i]->arr[i] := element->arr[i]
//																			$ if (i=0) then
//																					region := region SetDiff {element};
//																					elements := SetDiffElem (elements, SingleElem(value));
//																				endif
//																			$
//																		endif
//																		i := i + 1;
//																	endwhile
//
//																	// set new header level
//																	while ( (maxLevel > 0) /\ (head->arr[maxLevel] = null) ) do
//																		maxLevel := maxLevel - 1;
//																	endwhile
//																endif
//															end
