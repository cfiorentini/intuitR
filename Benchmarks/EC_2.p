fof(EC, conjecture, 
(
~(p1 & p2) &
~(p2 & p1)
& (~p1 | p2)
) => (
~p1 | ~p2 | (~p1 | ~p2) |
~p2 | ~p1 | (~p2 | ~p1) | 
~p1 | ~p2 | (p2 => p1) )
).
