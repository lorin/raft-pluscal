------------------------------- MODULE Store -------------------------------
VARIABLE store
CONSTANTS WriteReq(_, _, _, _),
          WriteResp(_, _),
          ReadReq(_, _),
          ReadResp(_, _, _)

CONSTANTS Variables, Values

CONSTANT InitStore

\* Below isn't currently syntatically correct
ASSUME \A var \in Variables, val \in Values, stOld, stNew :
        /\ WriteReq(var, val, stOld, stNew)  \in BOOLEAN
        /\ WriteResp(var, val, stOld, stNew) \in BOOLEAN
        /\ ReadReq(var, stOld, stNew)        \in BOOLEAN
        /\ ReadResp(var, val, stOld, stNew)  \in BOOLEAN

=============================================================================
