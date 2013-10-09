
global
  int tick := 0
  int min := 0
  ghost int overtaken := 0
  ghost int interested := 0
  tid victim
  tid taker

assume
  victim != taker

procedure main ()
  int ticket :=0
begin
  while (1=1) do
        noncritical;
        {
          ticket := tick;
          tick   := tick + 1;
        } $ if (me = victim) then interested := 1; overtaken := 0; endif $

:active[

        await ticket = min
        $ if (me = taker /\ ticket = min /\ interested = 1) then overtaken := overtaken + 1; endif $
:crit[
        critical;
        min := min + 1
        $ if (me = victim) then interested := 0; overtaken := 0; endif $
:crit]

:active]

  endwhile

  return();
end
