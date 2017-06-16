---------------------------- MODULE Linearizable ----------------------------

CONSTANT MaxLen
CONSTANT Objects


\* Allowed operations
Ops == [Action: {Inv, Res}, Object: Objects]

\* All possible histories up to length MaxLen
Histories == UNION {[1..n -> Ops] : n \in 1..MaxLen}

IsAnExtensionOf(H', H) == FALSE

IsLegalSequentialHistory(H) == FALSE

AreEquivalent(H, J) == FALSE

Ordering(H) == {}

IsLinearizable(H) == 
    \E H', S \in Histories :  
        /\ IsAnExtensionOf(H', H)
        /\ IsLegalSequentialHistory(S)
        /\ AreEquivalent(Complete(H'), S)
        /\ Ordering(H) \subseteq Ordering(S)


=============================================================================
\* Modification History
\* Created Thu Jun 15 19:06:06 PDT 2017 by lhochstein
