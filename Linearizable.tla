---------------------------- MODULE Linearizable ----------------------------

EXTENDS Naturals, Sequences, TLC

CONSTANT MaxLen
CONSTANT Objects
CONSTANT Processes
CONSTANTS Inv, Res


\* Allowed operations
Ops == [process: Processes, side: {Inv, Res}, object: Objects]

(*
--algorithm MultipleWriters

variable history = << >>;

define 
\* All possible histories up to length MaxLen
Histories == UNION {[1..n -> Ops] : n \in 0..MaxLen} 

IsAnExtensionOf(Hp, H) == LET N==Len(H) IN
                            /\ Len(Hp) \geq N
                            /\ SubSeq(Hp, 1, N) = H
                            /\ \A i \in Len(H)+1..Len(Hp) : Hp[i] \in Ops

\* A history H is sequential if:
\* 
\* 1. The first event of H is an invocation.
\* 2.  Each invocation, except possibly the last, is immediately followed by
\* a matching response. Each response is immediately preceded by a matching
\* invocation.

IsSequentialHistory(H) ==
\/ H = << >> 
\/  /\ H[1].side = Inv
    /\ \A i \in 1..Len(H) : 
        /\ (H[i].side = Inv) =>   \/ i = Len(H)
                                    \/  /\ H[i+1].side = Res
                                        /\ H[i+1].process = H[i].process
                                        /\ H[i+1].object = H[i].object
                                   
        /\ (H[i].side = Res) =>  /\ H[i-1].side = Inv
                                    /\ H[i-1].process = H[i].process
                                    /\ H[i-1].object = H[i].object

AreEquivalent(H, J) == H = J

AllInvocationsHaveMatchingResponses(H) ==
    \A i \in 1..Len(H) : (H[i].side = Inv) =>
        \E j \in 1+1..Len(H) :  /\ H[j].side = Res
                                /\ H[j].object = H[i].object
                                /\ H[j].process = H[i].process

Subsequences(H) == {SubSeq(H, 1, n) : n \in 0..Len(H)}

Complete(H) == CHOOSE h \in Subsequences(H) :
    /\ AllInvocationsHaveMatchingResponses(h) 
    /\ \A j \in Subsequences(H) : AllInvocationsHaveMatchingResponses(j) => Len(h) \geq Len(j)

Ordering(H) == {}

IsLinearizable(H) == 
\/  H = << >>
\/  \E Hp, S \in Histories :  
      /\ IsAnExtensionOf(Hp, H)
      /\ IsSequentialHistory(S)
      /\ AreEquivalent(Complete(Hp), S)
      /\ Ordering(H) \subseteq Ordering(S)

end define

process Proc \in Processes
variable obj \in Objects;
begin
    c1: history := Append(history, [process|->self, side|->Inv, object|->obj]);
    c2: history := Append(history, [process|->self, side|->Res, object|->obj]);
end process

end algorithm

*)
\* BEGIN TRANSLATION
VARIABLES history, pc

(* define statement *)
Histories == UNION {[1..n -> Ops] : n \in 0..MaxLen}

IsAnExtensionOf(Hp, H) == LET N==Len(H) IN
                            /\ Len(Hp) \geq N
                            /\ SubSeq(Hp, 1, N) = H
                            /\ \A i \in Len(H)+1..Len(Hp) : Hp[i] \in Ops








IsSequentialHistory(H) ==
\/ H = << >>
\/  /\ H[1].action = Inv
    /\ \A i \in 1..Len(H) :
        /\ (H[i].action = Inv) =>   \/ i = Len(H)
                                    \/  /\ H[i+1].action = Res
                                        /\ H[i+1].process = H[i].process
                                        /\ H[i+1].object = H[i].object

        /\ (H[i].action = Res) =>  /\ H[i-1].action = Inv
                                    /\ H[i-1].process = H[i].process
                                    /\ H[i-1].object = H[i].object

AreEquivalent(H, J) == H = J

AllInvocationsHaveMatchingResponses(H) ==
    \A i \in 1..Len(H) : (H[i].action = Inv) =>
        \E j \in 1+1..Len(H) :  /\ H[j].action = Res
                                /\ H[j].object = H[i].object
                                /\ H[j].process = H[i].process

Subsequences(H) == {SubSeq(H, 1, n) : n \in 0..Len(H)}

Complete(H) == CHOOSE h \in Subsequences(H) :
    /\ AllInvocationsHaveMatchingResponses(h)
    /\ \A j \in Subsequences(H) : AllInvocationsHaveMatchingResponses(j) => Len(h) \geq Len(j)

Ordering(H) == {}

IsLinearizable(H) ==
\/  H = << >>
\/  \E Hp, S \in Histories :
      /\ IsAnExtensionOf(Hp, H)
      /\ IsSequentialHistory(S)
      /\ AreEquivalent(Complete(Hp), S)
      /\ Ordering(H) \subseteq Ordering(S)

VARIABLE obj

vars == << history, pc, obj >>

ProcSet == (Processes)

Init == (* Global variables *)
        /\ history = << >>
        (* Process Proc *)
        /\ obj \in [Processes -> Objects]
        /\ pc = [self \in ProcSet |-> "c1"]

c1(self) == /\ pc[self] = "c1"
            /\ history' = Append(history, [process|->self, action|->Inv, object|->obj[self]])
            /\ pc' = [pc EXCEPT ![self] = "c2"]
            /\ obj' = obj

c2(self) == /\ pc[self] = "c2"
            /\ history' = Append(history, [process|->self, action|->Res, object|->obj[self]])
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ obj' = obj

Proc(self) == c1(self) \/ c2(self)

Next == (\E self \in Processes: Proc(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION



=============================================================================
\* Modification History
\* Last modified Sat Jun 17 11:48:13 PDT 2017 by lhochstein
\* Created Thu Jun 15 19:06:06 PDT 2017 by lhochstein
