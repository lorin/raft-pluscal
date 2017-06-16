---------------------------- MODULE Linearizable ----------------------------

EXTENDS Naturals, Sequences

CONSTANT MaxLen
CONSTANT Objects
CONSTANT Processes
CONSTANTS Inv, Res


\* Allowed operations
Ops == [Process: Processes, Action: {Inv, Res}, Object: Objects]

(*
--algorithm MultipleWriters

variable h = <<>>;

define 
\* All possible histories up to length MaxLen
Histories == UNION {[1..n -> Ops] : n \in 1..MaxLen}

IsAnExtensionOf(Hp, H) == LET N=Len(H) IN
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
    /\ H[1][Action] == Inv
    /\ \A i \in 1..Len(H) : 
        /\ (H[i][Action] = Inv) =>  \/  /\ H[i+1][Action] = Res
                                        /\ H[i+1][Process] = H[i][Process]
                                        /\ H[i+1][Object] = H[i][Object]
                                    \/ i = Len(H)
        /\ (H[i][Action] = Res) =>  /\ H[i-1][Action] = Inv
                                    /\ H[i-1][Process] = H[i][Process]
                                    /\ H[i-1][Object] = H[i][Object]

AreEquivalent(H, J) == H = J

AllInvocationsHaveMatchingResponses(H) ==
    \A i \in 1..Len(H) : (H[i][Action] = Inv) =>
        \E j \in 1+1..Len(H) :  /\ H[j][Action] = Res
                                /\ H[j][Object] = H[i][Object]
                                /\ H[j][Process] = H[i][Process]
        

Subsequences(H) = {SubSeq(H, 1, n) : n \in 1..Len(H)}

Complete(H) == CHOOSE h \in Subsequences(H) :
    /\ AllInvocationsHaveMatchingResponses(h) 
    /\ \A j \in Subsequences(H) : AllInvocationsHaveMatchingResponses(j) => Len(h) /geq Len(j)

Ordering(H) == {}

IsLinearizable(H) == 
    \E Hp, S \in Histories :  
        /\ IsAnExtensionOf(Hp, H)
        /\ IsSequentialHistory(S)
        /\ AreEquivalent(Complete(Hp), S)
        /\ Ordering(H) \subseteq Ordering(S)

end define

process Proc \in Processes
variable obj \in Objects;
begin
    c1: h := Append(h, [Process|->self, Action|->Inv, Object|->obj]);
    c2: h := Append(h, [Process|->self, Action|->Res, Object|->obj]);
end process

end algorithm

*)
\* BEGIN TRANSLATION
VARIABLES h, pc

(* define statement *)
Histories == UNION {[1..n -> Ops] : n \in 1..MaxLen}

IsAnExtensionOf(Hp, H) == FALSE

IsLegalSequentialHistory(H) == FALSE

AreEquivalent(H, J) == FALSE

Complete(H) == <<>>

Ordering(H) == {}

IsLinearizable(H) ==
    \E Hp, S \in Histories :
        /\ IsAnExtensionOf(Hp, H)
        /\ IsLegalSequentialHistory(S)
        /\ AreEquivalent(Complete(Hp), S)
        /\ Ordering(H) \subseteq Ordering(S)

VARIABLE obj

vars == << h, pc, obj >>

ProcSet == (Processes)

Init == (* Global variables *)
        /\ h = <<>>
        (* Process Proc *)
        /\ obj \in [Processes -> Objects]
        /\ pc = [self \in ProcSet |-> "c1"]

c1(self) == /\ pc[self] = "c1"
            /\ h' = Append(h, [Process|->self, Action|->Inv, Object|->obj[self]])
            /\ pc' = [pc EXCEPT ![self] = "c2"]
            /\ obj' = obj

c2(self) == /\ pc[self] = "c2"
            /\ h' = Append(h, [Process|->self, Action|->Res, Object|->obj[self]])
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
\* Last modified Thu Jun 15 21:18:57 PDT 2017 by lhochstein
\* Created Thu Jun 15 19:06:06 PDT 2017 by lhochstein
