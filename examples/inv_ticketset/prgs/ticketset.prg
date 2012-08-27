global
  int avail := 0
  intSet bag := EmptySetInt
  ghost intSet lower := EmptySetInt

procedure main ()
	int ticket := 0
begin

  while true do

        noncritical;
        {
          ticket := avail;
          avail := avail + 1;
					bag := UnionInt (bag, SingleInt(avail));
				}

:active[

        await (setIntMin(bag) = ticket);
:crit[
        critical;
				bag := SetDiffInt (bag, SingleInt(ticket));
:crit]
:active]

  endwhile

	return ();
end
