-------------------------- MODULE SequentialStore --------------------------
EXTENDS Naturals
CONSTANTS N
CONSTANTS Variables, Values
CONSTANT NoVal

(*
--algorithm SequentialStore

variables
    storeIsIdle = TRUE,
    storeData = [x \in Variables |-> NoVal],
    seq = [client \in 1..N |-> 0],
    request,
    response;

macro sendReadRequest(var) begin
    request := [client|->self, seq|->seq[self], type|->"Read", var|->var, val|->NoVal];
end macro;

macro sendWriteRequest(var, val) begin
    request := [client|->self, seq|->seq[self], type|->"Write", var|->var, val|->val];
end macro;

macro awaitResponse() begin
    await response.client = self /\ response.seq = seq[self];
end macro;


process Client \in 1..N
begin
c1: await storeIsIdle;
c2: storeIsIdle := FALSE;
c3: seq[self] := seq[self] + 1;
c4: either
        with var \in Variables do
            sendReadRequest(var);
        end with;
    or
        with var \in Variables, val \in Values do
            sendWriteRequest(var, val);
        end with;
    end either;
c5: awaitResponse();
end process

process Store = 0
begin
s1: await ~storeIsIdle;
    if request.type = "Read" then
        response := [client|->request.client, seq|->request.seq, type|->"Read", var|->request.var, val|->storeData[request.var]];
    else \* it's a write
        storeData[request.var] := request.val;
        response := [client|->request.client, seq|->request.seq, type|->"Write", var|->request.var, val|->request.val];
    end if;
s2: storeIsIdle := TRUE;
end process
end algorithm

*)


=============================================================================
