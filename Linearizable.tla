---------------------------- MODULE Linearizable ----------------------------

EXTENDS Naturals, Sequences

CONSTANT MaxLen
CONSTANT Objects
CONSTANT Processes
CONSTANTS Inv, Res


\* Allowed operations
Ops == [Process: Processes, Action: {Inv, Res}, Object: Objects]

(*
--algorithm MultipleAccessors

variable h = <<>>;

define 
\* All possible histories up to length MaxLen
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
