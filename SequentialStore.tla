-------------------------- MODULE SequentialStore --------------------------
EXTENDS Naturals, Sequences
CONSTANTS N
CONSTANTS Variables, Values
CONSTANT NoVal

CONSTANTS ReadOp, WriteOp
CONSTANTS RequestType, ResponseType


(*
--algorithm SequentialStore

variables
    storeData = [x \in Variables |-> NoVal],
    seq = [client \in 1..N |-> 0],
    requestQueue = <<>>;
    responseQueues = [client \in 1..N |-> <<>>];
    log = <<>>;

define IsRead(i)  == /\ log[i].type = ResponseType
                     /\ log[i].op = ReadOp
                     /\ log[i].val \in Values

       IsWrite(i) == /\ log[i].type = ResponseType
                     /\ log[i].op = WriteOp
                     /\ log[i].val \in Values
        \* Every read of a variable must correspond to the most recent write of that variable
       ReadLastWrite == \A i \in 1..Len(log) : IsRead(i) =>
        (\E j \in 1..(i-1) :
            /\ IsWrite(j)
            /\ log[i].var = log[j].var
            /\ log[i].val = log[j].val
            /\ ~ (\E k \in (j+1)..(i-1) : /\ log[i].var = log[k].var
                                          /\ log[i].val # log[k].val))
end define;

macro sendRequest(r) begin
    requestQueue := Append(requestQueue, r);
    log := Append(log, r);
end macro;

macro sendReadRequest(var)
begin sendRequest([type|->RequestType, client|->self, seq|->seq[self], op|->ReadOp, var|->var, val|->NoVal]);
end macro;

macro sendWriteRequest(var, val)
begin sendRequest([type|->RequestType, client|->self, seq|->seq[self], op|->WriteOp, var|->var, val|->val]);
end macro;

macro awaitResponse()
begin await Len(responseQueues[self]) > 0;
      log := Append(log, Head(responseQueues[self]));
      responseQueues[self] := Tail(responseQueues[self]);
end macro;

macro awaitPendingRequest()
begin await Len(requestQueue) > 0;
end macro;

macro getNextRequest()
begin request := Head(requestQueue);
      requestQueue := Tail(requestQueue)
end macro;

macro clearResponseQueue()
begin
    responseQueues[self] := <<>>;
end macro;

process Client \in 1..N
begin
c1: seq[self] := seq[self] + 1;
c2: either
        with var \in Variables do
            sendReadRequest(var);
        end with;
    or
        with var \in Variables, val \in Values do
            sendWriteRequest(var, val);
        end with;
    end either;
c4: awaitResponse();
c5: goto c1;
end process

process Store = 0
variables request, response;
begin
s1: awaitPendingRequest();
s2: getNextRequest();
s3: if request.op = ReadOp then
        response := [type|->ResponseType, client|->request.client, seq|->request.seq, op|->ReadOp, var|->request.var, val|->storeData[request.var]];
      else \* it's a write
        storeData[request.var] := request.val;
        response := [type|->ResponseType, client|->request.client, seq|->request.seq, op|->WriteOp, var|->request.var, val|->request.val];
      end if;
s4: responseQueues[response.client] := Append(responseQueues[response.client], response);
s5: goto s1;
end process

end algorithm

*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES storeIsIdle, storeData, seq, request, response, log, pc

(* define statement *)
IsRead(i)  == log[i].isResponse /\ log[i].op = "Read"  /\ log[i].val \in Values
IsWrite(i) == log[i].isResponse /\ log[i].op = "Write" /\ log[i].val \in Values

ReadLastWrite == \A i \in 1..Len(log) : IsRead(i) =>
 (\E j \in 1..(i-1) :
     /\ IsWrite(j)
     /\ log[i].var = log[j].var
     /\ log[i].val = log[j].val
     /\ ~ (\E k \in (j+1)..(i-1) : /\ log[i].var = log[k].var
                                   /\ log[i].val # log[k].val))


vars == << storeIsIdle, storeData, seq, request, response, log, pc >>

ProcSet == (1..N) \cup {0}

Init == (* Global variables *)
        /\ storeIsIdle = TRUE
        /\ storeData = [x \in Variables |-> NoVal]
        /\ seq = [client \in 1..N |-> 0]
        /\ request = defaultInitValue
        /\ response = defaultInitValue
        /\ log = <<>>
        /\ pc = [self \in ProcSet |-> CASE self \in 1..N -> "c1"
                                        [] self = 0 -> "s1"]

c1(self) == /\ pc[self] = "c1"
            /\ storeIsIdle
            /\ pc' = [pc EXCEPT ![self] = "c2"]
            /\ UNCHANGED << storeIsIdle, storeData, seq, request, response,
                            log >>

c2(self) == /\ pc[self] = "c2"
            /\ storeIsIdle' = FALSE
            /\ pc' = [pc EXCEPT ![self] = "c3"]
            /\ UNCHANGED << storeData, seq, request, response, log >>

c3(self) == /\ pc[self] = "c3"
            /\ seq' = [seq EXCEPT ![self] = seq[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "c4"]
            /\ UNCHANGED << storeIsIdle, storeData, request, response, log >>

c4(self) == /\ pc[self] = "c4"
            /\ \/ /\ \E var \in Variables:
                       /\ request' = [client|->self, seq|->seq[self], op|->"Read", var|->var, val|->NoVal, isResponse|->FALSE]
                       /\ log' = Append(log, request')
               \/ /\ \E var \in Variables:
                       \E val \in Values:
                         /\ request' = [client|->self, seq|->seq[self], op|->"Write", var|->var, val|->val, isResponse|->FALSE]
                         /\ log' = Append(log, request')
            /\ pc' = [pc EXCEPT ![self] = "c5"]
            /\ UNCHANGED << storeIsIdle, storeData, seq, response >>

c5(self) == /\ pc[self] = "c5"
            /\ response.client = self /\ response.seq = seq[self]
            /\ log' = Append(log, response)
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << storeIsIdle, storeData, seq, request, response >>

Client(self) == c1(self) \/ c2(self) \/ c3(self) \/ c4(self) \/ c5(self)

s1 == /\ pc[0] = "s1"
      /\ ~storeIsIdle
      /\ IF request.op = "Read"
            THEN /\ response' = [client|->request.client, seq|->request.seq, op|->"Read", var|->request.var, val|->storeData[request.var], isResponse|->TRUE]
                 /\ UNCHANGED storeData
            ELSE /\ storeData' = [storeData EXCEPT ![request.var] = request.val]
                 /\ response' = [client|->request.client, seq|->request.seq, op|->"Write", var|->request.var, val|->request.val, isResponse|->TRUE]
      /\ pc' = [pc EXCEPT ![0] = "s2"]
      /\ UNCHANGED << storeIsIdle, seq, request, log >>

s2 == /\ pc[0] = "s2"
      /\ storeIsIdle' = TRUE
      /\ pc' = [pc EXCEPT ![0] = "Done"]
      /\ UNCHANGED << storeData, seq, request, response, log >>

Store == s1 \/ s2

Next == Store
           \/ (\E self \in 1..N: Client(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
