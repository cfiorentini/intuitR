fof(negEC, conjecture, 
(
~(p1 & p2) &
~(p2 & p3) &
~(p3 & p4) &
~(p4 & p5) &
~(p5 & p1)
) => (
~p1 | ~p2 | (~p1 | ~p2) |
~p2 | ~p3 | (~p2 | ~p3) |
~p3 | ~p4 | (~p3 | ~p4) |
~p4 | ~p5 | (~p4 | ~p5) |
~p5 | ~p1 | (~p5 | ~p1) )
).
