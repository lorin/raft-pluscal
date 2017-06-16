---------------------------- MODULE Linearizable ----------------------------

EXTENDS Naturals, Sequences

CONSTANT MaxLen
CONSTANT Objects
CONSTANT Processes
CONSTANTS Inv, Res

VARIABLE h


\* Allowed operations
Ops == [Process: Processes, Action: {Inv, Res}, Object: Objects]

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


Init == /\ h = <<>>
Next == /\  h' = Append(h, CHOOSE op \in Ops : TRUE)
        /\  Len(h') \leq MaxLen


=============================================================================
\* Modification History
\* Last modified Thu Jun 15 20:32:00 PDT 2017 by lhochstein
\* Created Thu Jun 15 19:06:06 PDT 2017 by lhochstein
