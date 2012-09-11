
global
  int tick := 0
  int min := 0
  bool v

procedure main ()
  int ticket :=0
begin
  b := true;

  if (false = true) then
    skip;
    return (false);
  endif

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
