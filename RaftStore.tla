----------------------------- MODULE RaftStore -----------------------------
EXTENDS Sequences

CONSTANT Servers
CONSTANT null

CONSTANTS FollowerState, CandidateState, LeaderState

CONSTANTS AppendEntriesRequest, RequestVoteRequest, AppendEntriesResponse, RequestVoteResponse

(*
--algorithm Raft
variables log = [s \in Servers |-> <<>>],
          commitIndex = [s \in Servers |-> 0];

define
    Min(m,n) == IF m < n THEN m ELSE n
end define;

macro RespondAppendEntries(sender, receiver, term, success)
begin
rpcQueue[r.receiver] := Append(rpcQueue[r.receiver],
                                [sender|->sender,
                                 receiver|->receiver,
                                 type|->AppendEntriesResponse,term|->term,
                                 success|->success]);
end macro;

procedure ActAsLeader(leaderLastLogIndex)
variables nextIndex = [s \in Severs |-> leaderLastLogIndex+1],
          matchIndex = [s \in Servers |-> 0],
          rpcQueue = [s \in Servers |-> <<>>];
begin
l1: skip;
end procedure;


procedure ActAsFollower(currentTerm)
variable request;
begin
f1: either
        await Len(rpcQueue[self])>0;
        r := Head(rpcQueue[self]);
        rpcQueue[self] := Tail(rpcQueue[self]);
    or
        electionTimeoutElapses();
        return;
    end either;
f2:
    if r.type = AppendEntriesRequest then
        if r.term < currentTerm then
            RespondAppendEntries(self, r.sender, currentTerm, FALSE);
        elsif Len(log[self]) < [r.prevLogIndex] then
            RespondAppendEntries(self, r.sender, currentTerm, FALSE);
        elsif log[self][r.prevLogIndex].term /= r.prevLogTerm then
            log[self] := SubSeq(log[self], 1, r.prevLogIndex-1);
            RespondAppendEntries(self, r.sender, currentTerm, FALSE);
        else
            log[self] := log[self] \o r.entries;
        end if;
        if r.leaderCommit > commitIndex[self] then
            commitIndex[self] := Min(commitIndex[self], Len(log[self]));
        end if;
    else \* RequestVoteRpc
        skip;
    end if;
end procedure;

macro electionTimeoutElapses()
begin
    state = CandidateState;
end macro;

macro reboot()
    commitIndex[self] := 0;
    lastApplied := 0;
    state := FollowerState;
    goto s1;
begin
end macro;

macro applyToStateMachine(x)
begin skip;
end macro;


process Server \in Servers
variables currentTerm = 0,
          votedFor = null,
          commitIndex = 0,
          lastApplied = 0,
          state = FollowerState,
          request,
          response;
begin
s1: if state = FollowerState
    then call ActAsFollower(currentTerm);
    else if state = LeaderState
    then call ActAsLeader(Len(log[self]));
    else call ActAsCandidate();
    end if;
s2: goto s1;


end process
end algorithm

*)


=============================================================================
\* Modification History
\* Created Tue Apr 04 21:01:38 PDT 2017 by lorin
