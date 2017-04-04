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
    requestQueue = <<>>;
    responseQueues = [client \in 1..N |-> <<>>];
    log = <<>>;
    mutex = 0;

define IsRead(i, var, val)  == /\ log[i].type = ResponseType
                               /\ log[i].op = ReadOp
                               /\ log[i].var = var
                               /\ log[i].val = val

       IsWrite(i, var, val) == /\ log[i].type = ResponseType
                               /\ log[i].op = WriteOp
                               /\ log[i].var = var
                               /\ log[i].val = val

        \* Every read of a variable must correspond to the most recent write of that variable
       ReadLastWrite == \A i \in 1..Len(log), var \in Variables, val \in Values :
           IsRead(i, var, val) =>
               \E j \in 1..(i-1) : /\ IsWrite(j, var, val)
                                   /\ ~ \E k \in (j+1)..(i-1), v \in Values \ {val}: IsWrite(k, var, v)

       Message(type, client, op, var, val) ==
           [type|->type, client|->client, op|->op, var|->var, val|->val]
end define;

macro sendRequest(msg) begin
    requestQueue := Append(requestQueue, msg);
    log := Append(log, msg);
end macro;

macro sendReadRequest(var)
begin sendRequest(Message(RequestType, self, ReadOp, var, NoVal));
end macro;

macro sendWriteRequest(var, val)
begin sendRequest(Message(RequestType, self, WriteOp, var, val));
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

macro acquireMutex()
begin await mutex = 0;
      mutex := self;
end macro;

macro releaseMutex()
begin mutex := 0;
end macro;

process Client \in 1..N
begin
c1: acquireMutex();
c2: with var \in Variables, val \in Values do
        either sendReadRequest(var);
        or sendWriteRequest(var, val)
        end either;
    end with;
c3: awaitResponse();
c4: releaseMutex();
    goto c1;
end process

process Store = 0
variables request,response;
begin
s1: awaitPendingRequest();
s2: getNextRequest();
s3: if request.op = ReadOp then
        response := Message(ResponseType, request.client, ReadOp, request.var, storeData[request.var]);
    else \* it's a write
        storeData[request.var] := request.val;
        response := Message(ResponseType, request.client, WriteOp, request.var, request.val);
    end if;
s4: responseQueues[response.client] := Append(responseQueues[response.client], response);
s5: goto s1;
end process

end algorithm

*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES storeData, requestQueue, responseQueues, log, mutex, pc

(* define statement *)
IsRead(i, var, val)  == /\ log[i].type = ResponseType
                        /\ log[i].op = ReadOp
                        /\ log[i].var = var
                        /\ log[i].val = val

IsWrite(i, var, val) == /\ log[i].type = ResponseType
                        /\ log[i].op = WriteOp
                        /\ log[i].var = var
                        /\ log[i].val = val


ReadLastWrite == \A i \in 1..Len(log), var \in Variables, val \in Values :
    IsRead(i, var, val) =>
        \E j \in 1..(i-1) : /\ IsWrite(j, var, val)
                            /\ ~ \E k \in (j+1)..(i-1), v \in Values \ {val}: IsWrite(k, var, v)

Message(type, client, seq, op, var, val) ==
    [type|->type, client|->client, seq|->seq, op|->op, var|->var, val|->val]

VARIABLES seq, request, response

vars == << storeData, requestQueue, responseQueues, log, mutex, pc, seq, 
           request, response >>

ProcSet == (1..N) \cup {0}

Init == (* Global variables *)
        /\ storeData = [x \in Variables |-> NoVal]
        /\ requestQueue = <<>>
        /\ responseQueues = [client \in 1..N |-> <<>>]
        /\ log = <<>>
        /\ mutex = 0
        (* Process Client *)
        /\ seq = [self \in 1..N |-> 0]
        (* Process Store *)
        /\ request = defaultInitValue
        /\ response = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self \in 1..N -> "c1"
                                        [] self = 0 -> "s1"]

c1(self) == /\ pc[self] = "c1"
            /\ mutex = 0
            /\ mutex' = self
            /\ pc' = [pc EXCEPT ![self] = "c2"]
            /\ UNCHANGED << storeData, requestQueue, responseQueues, log, seq, 
                            request, response >>

c2(self) == /\ pc[self] = "c2"
            /\ seq' = [seq EXCEPT ![self] = seq[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "c3"]
            /\ UNCHANGED << storeData, requestQueue, responseQueues, log, 
                            mutex, request, response >>

c3(self) == /\ pc[self] = "c3"
            /\ \E var \in Variables:
                 \/ /\ requestQueue' = Append(requestQueue, (Message(RequestType, self, seq[self], ReadOp, var, NoVal)))
                    /\ log' = Append(log, (Message(RequestType, self, seq[self], ReadOp, var, NoVal)))
                 \/ /\ \E val \in Values:
                         /\ requestQueue' = Append(requestQueue, (Message(RequestType, self, seq[self], WriteOp, var, val)))
                         /\ log' = Append(log, (Message(RequestType, self, seq[self], WriteOp, var, val)))
            /\ pc' = [pc EXCEPT ![self] = "c5"]
            /\ UNCHANGED << storeData, responseQueues, mutex, seq, request, 
                            response >>

c5(self) == /\ pc[self] = "c5"
            /\ Len(responseQueues[self]) > 0
            /\ log' = Append(log, Head(responseQueues[self]))
            /\ responseQueues' = [responseQueues EXCEPT ![self] = Tail(responseQueues[self])]
            /\ pc' = [pc EXCEPT ![self] = "c6"]
            /\ UNCHANGED << storeData, requestQueue, mutex, seq, request, 
                            response >>

c6(self) == /\ pc[self] = "c6"
            /\ mutex' = 0
            /\ pc' = [pc EXCEPT ![self] = "c1"]
            /\ UNCHANGED << storeData, requestQueue, responseQueues, log, seq, 
                            request, response >>

Client(self) == c1(self) \/ c2(self) \/ c3(self) \/ c5(self) \/ c6(self)

s1 == /\ pc[0] = "s1"
      /\ Len(requestQueue) > 0
      /\ pc' = [pc EXCEPT ![0] = "s2"]
      /\ UNCHANGED << storeData, requestQueue, responseQueues, log, mutex, seq, 
                      request, response >>

s2 == /\ pc[0] = "s2"
      /\ request' = Head(requestQueue)
      /\ requestQueue' = Tail(requestQueue)
      /\ pc' = [pc EXCEPT ![0] = "s3"]
      /\ UNCHANGED << storeData, responseQueues, log, mutex, seq, response >>

s3 == /\ pc[0] = "s3"
      /\ IF request.op = ReadOp
            THEN /\ response' = [type|->ResponseType,
                                 client|->request.client,
                                 seq|->request.seq,
                                 op|->ReadOp,
                                 var|->request.var,
                                 val|->storeData[request.var]]
                 /\ UNCHANGED storeData
            ELSE /\ storeData' = [storeData EXCEPT ![request.var] = request.val]
                 /\ response' = [type|->ResponseType, client|->request.client, seq|->request.seq, op|->WriteOp, var|->request.var, val|->request.val]
      /\ pc' = [pc EXCEPT ![0] = "s4"]
      /\ UNCHANGED << requestQueue, responseQueues, log, mutex, seq, request >>

s4 == /\ pc[0] = "s4"
      /\ responseQueues' = [responseQueues EXCEPT ![response.client] = Append(responseQueues[response.client], response)]
      /\ pc' = [pc EXCEPT ![0] = "s5"]
      /\ UNCHANGED << storeData, requestQueue, log, mutex, seq, request, 
                      response >>

s5 == /\ pc[0] = "s5"
      /\ pc' = [pc EXCEPT ![0] = "s1"]
      /\ UNCHANGED << storeData, requestQueue, responseQueues, log, mutex, seq, 
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
