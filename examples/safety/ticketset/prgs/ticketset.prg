global
  int avail := 0
  intSet bag := iempty
  ghost intSet lower := iempty

procedure main ()
  int ticket := 0
begin

  while true do

        noncritical;
        {
          ticket := avail;
          avail := avail + 1;
          bag := iunion (bag, isingle(avail));
        }

:active[

        await (setIntMin(bag) = ticket);
:crit[
        critical;
        bag := idiff (bag, isingle(ticket));
:crit]
:active]

  endwhile

  return ();
end
