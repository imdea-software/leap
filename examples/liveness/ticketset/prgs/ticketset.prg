global
  int avail := 0
  pairSet bag := spempty

procedure main ()
  int ticket := 0
begin

  while true do

        noncritical;
        {
          ticket := avail;
          avail := avail + 1;
          bag := spunion (bag, spsingle((avail,me)));
        }

:active[

        await (int_of (spmin(bag)) = ticket);
:crit[
        critical;
        bag := spdiff (bag, spsingle((ticket, me)));
:crit]
:active]

  endwhile

  return ();
end
