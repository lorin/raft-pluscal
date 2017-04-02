-------------------------- MODULE SequentialStore --------------------------
EXTENDS Naturals
CONSTANTS N

(*
--algorithm SequentialStore

variables
    storeIsIdle = TRUE;

macro sendReadRequest() begin
    skip ;
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
end algorithm

*)


=============================================================================
