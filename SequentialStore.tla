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
VARIABLES storeData, seq, requestQueue, responseQueues, log, pc

(* define statement *)
IsRead(i)  == /\ log[i].type = ResponseType
              /\ log[i].op = ReadOp
              /\ log[i].val \in Values

IsWrite(i) == /\ log[i].type = ResponseType
              /\ log[i].op = WriteOp
              /\ log[i].val \in Values

ReadLastWrite == \A i \in 1..Len(log) : IsRead(i) =>
 (\E j \in 1..(i-1) :
     /\ IsWrite(j)
     /\ log[i].var = log[j].var
     /\ log[i].val = log[j].val
     /\ ~ (\E k \in (j+1)..(i-1) : /\ log[i].var = log[k].var
                                   /\ log[i].val # log[k].val))

VARIABLES request, response

vars == << storeData, seq, requestQueue, responseQueues, log, pc, request, 
           response >>

ProcSet == (1..N) \cup {0}

Init == (* Global variables *)
        /\ storeData = [x \in Variables |-> NoVal]
        /\ seq = [client \in 1..N |-> 0]
        /\ requestQueue = <<>>
        /\ responseQueues = [client \in 1..N |-> <<>>]
        /\ log = <<>>
        (* Process Store *)
        /\ request = defaultInitValue
        /\ response = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self \in 1..N -> "c1"
                                        [] self = 0 -> "s1"]

c1(self) == /\ pc[self] = "c1"
            /\ seq' = [seq EXCEPT ![self] = seq[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "c2"]
            /\ UNCHANGED << storeData, requestQueue, responseQueues, log, 
                            request, response >>

c2(self) == /\ pc[self] = "c2"
            /\ \/ /\ \E var \in Variables:
                       /\ requestQueue' = Append(requestQueue, ([type|->RequestType, client|->self, seq|->seq[self], op|->ReadOp, var|->var, val|->NoVal]))
                       /\ log' = Append(log, ([type|->RequestType, client|->self, seq|->seq[self], op|->ReadOp, var|->var, val|->NoVal]))
               \/ /\ \E var \in Variables:
                       \E val \in Values:
                         /\ requestQueue' = Append(requestQueue, ([type|->RequestType, client|->self, seq|->seq[self], op|->WriteOp, var|->var, val|->val]))
                         /\ log' = Append(log, ([type|->RequestType, client|->self, seq|->seq[self], op|->WriteOp, var|->var, val|->val]))
            /\ pc' = [pc EXCEPT ![self] = "c4"]
            /\ UNCHANGED << storeData, seq, responseQueues, request, response >>

c4(self) == /\ pc[self] = "c4"
            /\ Len(responseQueues[self]) > 0
            /\ log' = Append(log, Head(responseQueues[self]))
            /\ responseQueues' = [responseQueues EXCEPT ![self] = Tail(responseQueues[self])]
            /\ pc' = [pc EXCEPT ![self] = "c5"]
            /\ UNCHANGED << storeData, seq, requestQueue, request, response >>

c5(self) == /\ pc[self] = "c5"
            /\ pc' = [pc EXCEPT ![self] = "c1"]
            /\ UNCHANGED << storeData, seq, requestQueue, responseQueues, log, 
                            request, response >>

Client(self) == c1(self) \/ c2(self) \/ c4(self) \/ c5(self)

s1 == /\ pc[0] = "s1"
      /\ Len(requestQueue) > 0
      /\ pc' = [pc EXCEPT ![0] = "s2"]
      /\ UNCHANGED << storeData, seq, requestQueue, responseQueues, log, 
                      request, response >>

s2 == /\ pc[0] = "s2"
      /\ request' = Head(requestQueue)
      /\ requestQueue' = Tail(requestQueue)
      /\ pc' = [pc EXCEPT ![0] = "s3"]
      /\ UNCHANGED << storeData, seq, responseQueues, log, response >>

s3 == /\ pc[0] = "s3"
      /\ IF request.op = ReadOp
            THEN /\ response' = [type|->ResponseType, client|->request.client, seq|->request.seq, op|->ReadOp, var|->request.var, val|->storeData[request.var]]
                 /\ UNCHANGED storeData
            ELSE /\ storeData' = [storeData EXCEPT ![request.var] = request.val]
                 /\ response' = [type|->ResponseType, client|->request.client, seq|->request.seq, op|->WriteOp, var|->request.var, val|->request.val]
      /\ pc' = [pc EXCEPT ![0] = "s4"]
      /\ UNCHANGED << seq, requestQueue, responseQueues, log, request >>

s4 == /\ pc[0] = "s4"
      /\ responseQueues' = [responseQueues EXCEPT ![response.client] = Append(responseQueues[response.client], response)]
      /\ pc' = [pc EXCEPT ![0] = "s5"]
      /\ UNCHANGED << storeData, seq, requestQueue, log, request, response >>

s5 == /\ pc[0] = "s5"
      /\ pc' = [pc EXCEPT ![0] = "s1"]
      /\ UNCHANGED << storeData, seq, requestQueue, responseQueues, log, 
                      request, response >>

Store == s1 \/ s2 \/ s3 \/ s4 \/ s5

Next == Store
           \/ (\E self \in 1..N: Client(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
