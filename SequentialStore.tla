-------------------------- MODULE SequentialStore --------------------------
EXTENDS Naturals
CONSTANTS N
CONSTANTS Variables, Values
CONSTANT NoVal

(*
--algorithm SequentialStore

variables
    storeIsIdle = TRUE,
    responseIsReady = FALSE,
    storeData = [x \in Variables |-> NoVal],
    request,
    response;



macro sendReadRequest() begin
    with var \in Variables do
        request := [type|->"Read", var|->var, val|->NoVal];
    end with;

end macro;

macro awaitReadResponse() begin
    await responseIsReady ;
    responseIsReady := FALSE;
end macro;

macro sendWriteRequest() begin
    skip;
end macro;

macro awaitWriteResponse() begin
    await ResponseIsReady ;
    responseIsReady := FALSE;
end macro;

process Client \in 1..N
begin
c1: await storeIsIdle;
c2: storeIsIdle := FALSE;
    either
        sendReadRequest();
        car: awaitReadResponse();
    or
        sendWriteRequest();
        caw: awaitWriteResponse();
    end either ;
end process

process Store = 0
begin
s1: await ~storeIsIdle;
    if request.type = "Read" then
        response := [type|->"Read", var|->request.var, val->storeData[var]];
    else
        response := [type|->"Write", var->request.var, val->request.val];
    end if
    responseIsReady := TRUE;
s2: storeIsIdle := TRUE;
end process
end algorithm

*)


=============================================================================
