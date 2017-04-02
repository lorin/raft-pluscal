-------------------------- MODULE SequentialStore --------------------------
EXTENDS Naturals, Sequences
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
    log = <<>>;

define IsRead(i)  == log[i].isResponse /\ log[i].type = "Read"  /\ log[i].val \in Values
       IsWrite(i) == log[i].isResponse /\ log[i].type = "Write" /\ log[i].val \in Values
        \* Every read of a variable must correspond to the most recent write of that variable
       ReadLastWrite == \A i \in 1..Len(log) : IsRead(i) =>
        (\E j \in 1..(i-1) :
            /\ IsWrite(j)
            /\ log[i].var = log[j].var
            /\ log[i].val = log[j].val
            /\ ~ (\E k \in (j+1)..(i-1) : /\ log[i].var = log[k].var
                                          /\ log[i].val # log[k].val))
end define;

macro sendReadRequest(var) begin
    request := [client|->self, seq|->seq[self], type|->"Read", var|->var, val|->NoVal, isResponse|->FALSE];
    log := Append(log, request);
end macro;

macro sendWriteRequest(var, val) begin
    request := [client|->self, seq|->seq[self], type|->"Write", var|->var, val|->val, isResponse|->FALSE];
    log := Append(log, request);
end macro;

macro awaitResponse() begin
    await response.client = self /\ response.seq = seq[self];
    log := Append(log, response);
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
        response := [client|->request.client, seq|->request.seq, type|->"Read", var|->request.var, val|->storeData[request.var], isResponse|->TRUE];
    else \* it's a write
        storeData[request.var] := request.val;
        response := [client|->request.client, seq|->request.seq, type|->"Write", var|->request.var, val|->request.val, isResponse|->TRUE];
    end if;
s2: storeIsIdle := TRUE;
end process

end algorithm

*)

=============================================================================
