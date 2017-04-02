-------------------------- MODULE SequentialStore --------------------------
EXTENDS Naturals
CONSTANTS N
CONSTANTS Variables, Values
CONSTANT NoVal

(*
--algorithm SequentialStore

variables
    storeIsIdle = TRUE;
    storeData = [x \in Variables |-> NoVal];
    request;


macro sendReadRequest() begin
    with var \in Variables do
        request := [type|->"Read", var|->var, val|->NoVal];
    end with;

end macro;

macro awaitReadResponse() begin
    skip ;
end macro;

macro sendWriteRequest() begin
    skip ;
end macro;

macro awaitWriteResponse() begin
    skip ;
end macro;

process Client \in 1..N
begin
c1: await storeIsIdle;
c2: storeIsIdle := FALSE;
    either
        r1: sendReadRequest();
        r2: awaitReadResponse();
    or
        w1: sendWriteRequest();
        w2: awaitWriteResponse();
    end either ;
end process

process Store = 0
begin
s1: await ~storeIsIdle;
end process
end algorithm

*)


=============================================================================
