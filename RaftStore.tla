----------------------------- MODULE RaftStore -----------------------------
EXTENDS Naturals, Sequences

CONSTANT Servers
CONSTANT null

CONSTANTS FollowerState, CandidateState, LeaderState

CONSTANTS AppendEntriesRequest, RequestVoteRequest, AppendEntriesResponse, RequestVoteResponse

(*
--algorithm Raft
\* These are per-server but we make them global so procedures can modify them
variables log = [s \in Servers |-> <<>>],
          commitIndex = [s \in Servers |-> 0];

define
    Min(m,n) == IF m < n THEN m ELSE n
end define;

macro RespondAppendEntries(sender, receiver, term, success) begin
    rpcQueue[request.receiver] := Append(rpcQueue[request.receiver],
                                    [sender|->sender,
                                     receiver|->receiver,
                                     type|->AppendEntriesResponse,term|->term,
                                     success|->success]);
end macro;


macro electionTimeoutElapses() begin
    state := CandidateState;
end macro;

macro reboot() begin
    commitIndex[self] := 0;
    lastApplied := 0;
    state := FollowerState;
    goto s1;
end macro;

macro applyToStateMachine(x) begin
    skip;
end macro;

macro AppendEntries() begin
    if request.term < currentTerm then
        RespondAppendEntries(self, request.sender, currentTerm, FALSE);
    elsif Len(log[self]) < request.prevLogIndex then
        RespondAppendEntries(self, request.sender, currentTerm, FALSE);
    elsif log[self][request.prevLogIndex].term /= request.prevLogTerm then
        log[self] := SubSeq(log[self], 1, request.prevLogIndex-1);
        RespondAppendEntries(self, request.sender, currentTerm, FALSE);
    else
        log[self] := log[self] \o request.entries;
    end if;
    if request.leaderCommit > commitIndex[self] then
        commitIndex[self] := Min(commitIndex[self], Len(log[self]));
    end if;
end macro;

macro RequestVotes() begin
    skip;
end macro;


procedure ActAsLeader(leaderLastLogIndex)
variables nextIndex = [s \in Servers |-> leaderLastLogIndex+1],
          matchIndex = [s \in Servers |-> 0],
          rpcQueue = [s \in Servers |-> <<>>];
begin
l1: skip;
end procedure;

procedure ActAsCandidate() begin
c1: skip;
end procedure;


procedure ActAsFollower(currentTerm)
variable request;
begin
f1: either
        await Len(rpcQueue[self])>0;
        request := Head(rpcQueue[self]);
        rpcQueue[self] := Tail(rpcQueue[self]);
    or
        electionTimeoutElapses();
        return;
    end either;
f2:
    if request.type = AppendEntriesRequest then
        AppendEntries();
    else \* RequestVoteRpc
        RequestVotes();
    end if;
end procedure;


process Server \in Servers
variables currentTerm = 0,
          votedFor = null,
          lastApplied = 0,
          state = FollowerState,
          request,
          response;
begin
s1: if state = FollowerState then
        call ActAsFollower(currentTerm);
    elsif state = LeaderState then
        call ActAsLeader(Len(log[self]));
    else
        call ActAsCandidate();
    end if;
s2: goto s1;


end process
end algorithm

*)
\* BEGIN TRANSLATION
\* Process variable currentTerm of process Server at line 100 col 11 changed to currentTerm_
\* Process variable request of process Server at line 104 col 11 changed to request_
CONSTANT defaultInitValue
VARIABLES log, commitIndex, pc, stack

(* define statement *)
Min(m,n) == IF m < n THEN m ELSE n

VARIABLES leaderLastLogIndex, nextIndex, matchIndex, rpcQueue, currentTerm, 
          request, currentTerm_, votedFor, lastApplied, state, request_, 
          response

vars == << log, commitIndex, pc, stack, leaderLastLogIndex, nextIndex, 
           matchIndex, rpcQueue, currentTerm, request, currentTerm_, votedFor, 
           lastApplied, state, request_, response >>

ProcSet == (Servers)

Init == (* Global variables *)
        /\ log = [s \in Servers |-> <<>>]
        /\ commitIndex = [s \in Servers |-> 0]
        (* Procedure ActAsLeader *)
        /\ leaderLastLogIndex = [ self \in ProcSet |-> defaultInitValue]
        /\ nextIndex = [ self \in ProcSet |-> [s \in Servers |-> leaderLastLogIndex[self]+1]]
        /\ matchIndex = [ self \in ProcSet |-> [s \in Servers |-> 0]]
        /\ rpcQueue = [ self \in ProcSet |-> [s \in Servers |-> <<>>]]
        (* Procedure ActAsFollower *)
        /\ currentTerm = [ self \in ProcSet |-> defaultInitValue]
        /\ request = [ self \in ProcSet |-> defaultInitValue]
        (* Process Server *)
        /\ currentTerm_ = [self \in Servers |-> 0]
        /\ votedFor = [self \in Servers |-> null]
        /\ lastApplied = [self \in Servers |-> 0]
        /\ state = [self \in Servers |-> FollowerState]
        /\ request_ = [self \in Servers |-> defaultInitValue]
        /\ response = [self \in Servers |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "s1"]

l1(self) == /\ pc[self] = "l1"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "Error"]
            /\ UNCHANGED << log, commitIndex, stack, leaderLastLogIndex, 
                            nextIndex, matchIndex, rpcQueue, currentTerm, 
                            request, currentTerm_, votedFor, lastApplied, 
                            state, request_, response >>

ActAsLeader(self) == l1(self)

c1(self) == /\ pc[self] = "c1"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "Error"]
            /\ UNCHANGED << log, commitIndex, stack, leaderLastLogIndex, 
                            nextIndex, matchIndex, rpcQueue, currentTerm, 
                            request, currentTerm_, votedFor, lastApplied, 
                            state, request_, response >>

ActAsCandidate(self) == c1(self)

f1(self) == /\ pc[self] = "f1"
            /\ \/ /\ Len(rpcQueue[self][self])>0
                  /\ request' = [request EXCEPT ![self] = Head(rpcQueue[self][self])]
                  /\ rpcQueue' = [rpcQueue EXCEPT ![self][self] = Tail(rpcQueue[self][self])]
                  /\ pc' = [pc EXCEPT ![self] = "f2"]
                  /\ UNCHANGED <<stack, currentTerm, state>>
               \/ /\ state' = [state EXCEPT ![self] = CandidateState]
                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                  /\ request' = [request EXCEPT ![self] = Head(stack[self]).request]
                  /\ currentTerm' = [currentTerm EXCEPT ![self] = Head(stack[self]).currentTerm]
                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                  /\ UNCHANGED rpcQueue
            /\ UNCHANGED << log, commitIndex, leaderLastLogIndex, nextIndex, 
                            matchIndex, currentTerm_, votedFor, lastApplied, 
                            request_, response >>

f2(self) == /\ pc[self] = "f2"
            /\ IF request[self].type = AppendEntriesRequest
                  THEN /\ IF request[self].term < currentTerm[self]
                             THEN /\ rpcQueue' = [rpcQueue EXCEPT ![self][request[self].receiver] = Append(rpcQueue[self][request[self].receiver],
                                                                                                      [sender|->self,
                                                                                                       receiver|->(request[self].sender),
                                                                                                       type|->AppendEntriesResponse,term|->currentTerm[self],
                                                                                                       success|->FALSE])]
                                  /\ log' = log
                             ELSE /\ IF Len(log[self]) < request[self].prevLogIndex
                                        THEN /\ rpcQueue' = [rpcQueue EXCEPT ![self][request[self].receiver] = Append(rpcQueue[self][request[self].receiver],
                                                                                                                 [sender|->self,
                                                                                                                  receiver|->(request[self].sender),
                                                                                                                  type|->AppendEntriesResponse,term|->currentTerm[self],
                                                                                                                  success|->FALSE])]
                                             /\ log' = log
                                        ELSE /\ IF log[self][request[self].prevLogIndex].term /= request[self].prevLogTerm
                                                   THEN /\ log' = [log EXCEPT ![self] = SubSeq(log[self], 1, request[self].prevLogIndex-1)]
                                                        /\ rpcQueue' = [rpcQueue EXCEPT ![self][request[self].receiver] = Append(rpcQueue[self][request[self].receiver],
                                                                                                                            [sender|->self,
                                                                                                                             receiver|->(request[self].sender),
                                                                                                                             type|->AppendEntriesResponse,term|->currentTerm[self],
                                                                                                                             success|->FALSE])]
                                                   ELSE /\ log' = [log EXCEPT ![self] = log[self] \o request[self].entries]
                                                        /\ UNCHANGED rpcQueue
                       /\ IF request[self].leaderCommit > commitIndex[self]
                             THEN /\ commitIndex' = [commitIndex EXCEPT ![self] = Min(commitIndex[self], Len(log'[self]))]
                             ELSE /\ TRUE
                                  /\ UNCHANGED commitIndex
                  ELSE /\ TRUE
                       /\ UNCHANGED << log, commitIndex, rpcQueue >>
            /\ pc' = [pc EXCEPT ![self] = "Error"]
            /\ UNCHANGED << stack, leaderLastLogIndex, nextIndex, matchIndex, 
                            currentTerm, request, currentTerm_, votedFor, 
                            lastApplied, state, request_, response >>

ActAsFollower(self) == f1(self) \/ f2(self)

s1(self) == /\ pc[self] = "s1"
            /\ IF state[self] = FollowerState
                  THEN /\ /\ currentTerm' = [currentTerm EXCEPT ![self] = currentTerm_[self]]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ActAsFollower",
                                                                   pc        |->  "s2",
                                                                   request   |->  request[self],
                                                                   currentTerm |->  currentTerm[self] ] >>
                                                               \o stack[self]]
                       /\ request' = [request EXCEPT ![self] = defaultInitValue]
                       /\ pc' = [pc EXCEPT ![self] = "f1"]
                       /\ UNCHANGED << leaderLastLogIndex, nextIndex, 
                                       matchIndex, rpcQueue >>
                  ELSE /\ IF state[self] = LeaderState
                             THEN /\ /\ leaderLastLogIndex' = [leaderLastLogIndex EXCEPT ![self] = Len(log[self])]
                                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ActAsLeader",
                                                                              pc        |->  "s2",
                                                                              nextIndex |->  nextIndex[self],
                                                                              matchIndex |->  matchIndex[self],
                                                                              rpcQueue  |->  rpcQueue[self],
                                                                              leaderLastLogIndex |->  leaderLastLogIndex[self] ] >>
                                                                          \o stack[self]]
                                  /\ nextIndex' = [nextIndex EXCEPT ![self] = [s \in Servers |-> leaderLastLogIndex'[self]+1]]
                                  /\ matchIndex' = [matchIndex EXCEPT ![self] = [s \in Servers |-> 0]]
                                  /\ rpcQueue' = [rpcQueue EXCEPT ![self] = [s \in Servers |-> <<>>]]
                                  /\ pc' = [pc EXCEPT ![self] = "l1"]
                             ELSE /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ActAsCandidate",
                                                                           pc        |->  "s2" ] >>
                                                                       \o stack[self]]
                                  /\ pc' = [pc EXCEPT ![self] = "c1"]
                                  /\ UNCHANGED << leaderLastLogIndex, 
                                                  nextIndex, matchIndex, 
                                                  rpcQueue >>
                       /\ UNCHANGED << currentTerm, request >>
            /\ UNCHANGED << log, commitIndex, currentTerm_, votedFor, 
                            lastApplied, state, request_, response >>

s2(self) == /\ pc[self] = "s2"
            /\ pc' = [pc EXCEPT ![self] = "s1"]
            /\ UNCHANGED << log, commitIndex, stack, leaderLastLogIndex, 
                            nextIndex, matchIndex, rpcQueue, currentTerm, 
                            request, currentTerm_, votedFor, lastApplied, 
                            state, request_, response >>

Server(self) == s1(self) \/ s2(self)

Next == (\E self \in ProcSet:  \/ ActAsLeader(self) \/ ActAsCandidate(self)
                               \/ ActAsFollower(self))
           \/ (\E self \in Servers: Server(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Tue Apr 04 22:08:07 PDT 2017 by lorin
\* Created Tue Apr 04 21:01:38 PDT 2017 by lorin
