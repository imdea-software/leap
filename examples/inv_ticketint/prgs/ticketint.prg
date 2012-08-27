
global
  int tick := 0
  int min := 0

procedure main ()
  int ticket :=0
begin

  while (1=1) do

        noncritical;
        {
          ticket := tick;
          tick   := tick + 1;
        }

:active[

        await ticket = min;
:crit[
        critical;
        min := min + 1;
:crit]

:active]

  endwhile

	return();
end
