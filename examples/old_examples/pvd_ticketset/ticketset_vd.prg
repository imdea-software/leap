global
  int avail := 0
  intSet bag := EmptySetInt
  ghost intSet lower := EmptySetInt

procedure main ()
  int ticket
begin

  while true do

        noncritical;
        {
          ticket := avail;
          avail := avail + 1;
          bag := bag UnionInt SingleInt(avail);
        }

:active[

        await (setIntMin(bag) = ticket);
:crit[
        critical;
        bag := bag SetDiffInt SingleInt(ticket);
:crit]
:active]

  endwhile

end
