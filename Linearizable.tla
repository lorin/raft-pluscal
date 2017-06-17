---------------------------- MODULE Linearizable ----------------------------

EXTENDS Naturals, Sequences, TLC

CONSTANT MaxLen
CONSTANT Processes
CONSTANT Items
CONSTANTS Inv, Res
CONSTANT Enq, Deq
CONSTANT NoVal



\* Allowed operations
Ops == [method: {Enq, Deq}, item: Items \union {NoVal}, process: Processes, side: {Inv, Res}]

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
\* 2. Each invocation, except possibly the last, is immediately followed by
\*    a matching response. Each response is immediately preceded by a matching
\*    invocation.

IsSequentialHistory(H) ==
\/ H = << >> 
\/  /\ H[1].side = Inv
    /\ \A i \in 1..Len(H) : 
        /\ (H[i].side = Inv) =>   \/ i = Len(H)
                                  \/  /\ H[i+1].side = Res
                                      /\ H[i+1].process = H[i].process
                                   
        /\ (H[i].side = Res) =>  /\ H[i-1].side = Inv
                                    /\ H[i-1].process = H[i].process

\* Every dequeue must be matched by a corresponding enqueue
\* This assumes sequential, so we don't care about the side of the operation
IsLegalHistory(H) ==
    \A i \in 1..Len(H):
        H[i].method = Deq =>
            \E j \in 1..i-1: 
                /\ H[j].method = Enq
                /\ H[j].item = H[i].item
                /\  ~\E k \in j+1..i-1 : /\ H[k].method = Enq
                                         /\ H[k].item /= H[i].item 


\* Two histories are equivalent if every op that appears in one
\* history appears in the other
AreEquivalent(H, J) == 
    /\ Len(H) = Len(J)
    /\ \A i \in 1..Len(H): \E j \in 1..Len(J): H[i] = J[j]
    /\ \A i \in 1..Len(J): \E j \in 1..Len(H): J[i] = H[j]

AllInvocationsHaveMatchingResponses(H) ==
    \A i \in 1..Len(H) : (H[i].side = Inv) =>
        \E j \in 1+1..Len(H) :  /\ H[j].side = Res
                                /\ H[j].process = H[i].process

Subsequences(H) == {SubSeq(H, 1, n) : n \in 0..Len(H)}

Complete(H) == CHOOSE h \in Subsequences(H) :
    /\ AllInvocationsHaveMatchingResponses(h) 
    /\ \A j \in Subsequences(H) : AllInvocationsHaveMatchingResponses(j) => Len(h) \geq Len(j)

Ordering(H) == { }

IsLinearizable(H) == 
\/  H = << >>
\/  \E Hp, S \in Histories :  
      /\ IsAnExtensionOf(Hp, H)
      /\ IsSequentialHistory(S)
      /\ IsLegalHistory(S)
      /\ AreEquivalent(Complete(Hp), S)
      /\ Ordering(H) \subseteq Ordering(S)

end define

process Proc \in Processes
variable item \in Items;
begin
either
    e1: history := Append(history, [method|->Enq, item|->item, process|->self, side|->Inv]);
    e2: history := Append(history, [method|->Enq, item|->item, process|->self, side|->Res]);
or
    d1: history := Append(history, [method|->Deq, item|->NoVal, process|->self, side|->Inv]);
    d2: history := Append(history, [method|->Deq, item|->item, process|->self, side|->Res]);
end either;
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
\/  /\ H[1].side = Inv
    /\ \A i \in 1..Len(H) :
        /\ (H[i].side = Inv) =>   \/ i = Len(H)
                                  \/  /\ H[i+1].side = Res
                                      /\ H[i+1].process = H[i].process

        /\ (H[i].side = Res) =>  /\ H[i-1].side = Inv
                                    /\ H[i-1].process = H[i].process



IsLegalHistory(H) ==
    \A i \in 1..Len(H):
        H[i].method = Deq =>
            \E j \in 1..i-1:
                /\ H[j].method = Enq
                /\ H[j].item = H[i].item
                /\  ~\E k \in j+1..i-1 : /\ H[k].method = Enq
                                         /\ H[k].item /= H[i].item




AreEquivalent(H, J) ==
    /\ Len(H) = Len(J)
    /\ \A i \in 1..Len(H): \E j \in 1..Len(J): H[i] = J[j]
    /\ \A i \in 1..Len(J): \E j \in 1..Len(H): J[i] = H[j]

AllInvocationsHaveMatchingResponses(H) ==
    \A i \in 1..Len(H) : (H[i].side = Inv) =>
        \E j \in 1+1..Len(H) :  /\ H[j].side = Res
                                /\ H[j].process = H[i].process

Subsequences(H) == {SubSeq(H, 1, n) : n \in 0..Len(H)}

Complete(H) == CHOOSE h \in Subsequences(H) :
    /\ AllInvocationsHaveMatchingResponses(h)
    /\ \A j \in Subsequences(H) : AllInvocationsHaveMatchingResponses(j) => Len(h) \geq Len(j)

Ordering(H) == { }

IsLinearizable(H) ==
\/  H = << >>
\/  \E Hp, S \in Histories :
      /\ IsAnExtensionOf(Hp, H)
      /\ IsSequentialHistory(S)
      /\ IsLegalHistory(S)
      /\ AreEquivalent(Complete(Hp), S)
      /\ Ordering(H) \subseteq Ordering(S)

VARIABLE item

vars == << history, pc, item >>

ProcSet == (Processes)

Init == (* Global variables *)
        /\ history = << >>
        (* Process Proc *)
        /\ item \in [Processes -> Items]
        /\ pc = [self \in ProcSet |-> "l0"]

l0(self) == /\ pc[self] = "l0"
            /\ \/ /\ pc' = [pc EXCEPT ![self] = "e1"]
               \/ /\ pc' = [pc EXCEPT ![self] = "d1"]
            /\ UNCHANGED << history, item >>

e1(self) == /\ pc[self] = "e1"
            /\ history' = Append(history, [method|->enq, item|->item[self], process|->self, side|->Inv])
            /\ pc' = [pc EXCEPT ![self] = "e2"]
            /\ item' = item

e2(self) == /\ pc[self] = "e2"
            /\ history' = Append(history, [method|->enq, item|->item[self], process|->self, side|->Res])
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ item' = item

d1(self) == /\ pc[self] = "d1"
            /\ history' = Append(history, [method|->deq, item|->NoVal, process|->self, side|->Inv])
            /\ pc' = [pc EXCEPT ![self] = "d2"]
            /\ item' = item

d2(self) == /\ pc[self] = "d2"
            /\ history' = Append(history, [method|->deq, item|->item[self], process|->self, side|->Res])
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ item' = item

Proc(self) == l0(self) \/ e1(self) \/ e2(self) \/ d1(self) \/ d2(self)

Next == (\E self \in Processes: Proc(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION



=============================================================================
\* Modification History
\* Last modified Sat Jun 17 12:50:43 PDT 2017 by lhochstein
\* Created Thu Jun 15 19:06:06 PDT 2017 by lhochstein
