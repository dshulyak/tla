----------------------------- MODULE FastPaxos -----------------------------

EXTENDS Integers, FiniteSets, TLC

CONSTANTS Acceptors, Values

Rounds == Nat
Classic == {i \in Rounds: i % 2 = 0}
Fast == {i \in Rounds: i % 2 = 1}

any == CHOOSE v : v \notin Values
none == CHOOSE v : v \notin Values \cup {any}

Max(S) == CHOOSE i \in S : \A j \in S : j \leq i

Quorums == {a \in SUBSET Acceptors: Cardinality(a) * 2 > Cardinality(Acceptors)}
FastQuorums == {a \in SUBSET Acceptors: Cardinality(a)  * 4 >= Cardinality(Acceptors) * 3 }

GetQuorums(i) == IF i \in Classic THEN Quorums ELSE FastQuorums

VARIABLES messages,
          maxBallot,
          votedBallot,
          votedValue,
          proposed,
          leader
          
vars == <<messages, maxBallot, votedBallot, votedValue, proposed, leader>>

Init == /\ messages = {}
        /\ maxBallot = [a \in Acceptors |-> -1]
        /\ votedBallot = [a \in Acceptors |-> -1]
        /\ votedValue = [a \in Acceptors |-> none]
        /\ proposed = {}
        /\ leader \in [Acceptors -> BOOLEAN]

Send(m) == messages' = messages \cup {m}
Select(t, b) == {m \in messages: m.type = t /\ m.ballot = b}          
SelectQuorum(t, b, Q) == {m \in Select(t, b): m.acceptor \in Q}

Propose(v) == /\ v \notin proposed
              /\ proposed' = proposed \cup {v}
              /\ UNCHANGED <<messages, maxBallot, votedBallot, votedValue, leader>>
          
LeaderSelection == /\ leader' \in [Acceptors -> BOOLEAN]
                   /\ UNCHANGED <<messages, maxBallot, votedBallot, votedValue, proposed>>
          
P1a(a, b) == /\ Select("p1a", b) = {}
             /\ b \in Fast
             /\ leader[a]
             /\ Send([type |-> "p1a", ballot |-> b])
             /\ UNCHANGED <<maxBallot, votedBallot, votedValue, proposed, leader>>

P1b(a) == \E m \in messages:
             /\ m.type = "p1a"
             /\ m.ballot > maxBallot[a]
             /\ Send([type |-> "p1b", ballot |-> m.ballot,
                      acceptor |-> a, voted |-> votedBallot[a],
                      value |-> votedValue[a]])
             /\ maxBallot' = [maxBallot EXCEPT ![a] = m.ballot]
             /\ UNCHANGED <<votedBallot, votedValue, proposed, leader>>

(* 
pick a value for p2a (initial or coordinated recovery)
Value should be picked if:
- all voters from the highest round voted for one value
- if majority from classic quorum voted for the same value
otherwise Any will be picked
*)
Safe(S, v) == 
    LET k == Max({m.voted: m \in S})
        maxmsgs == {m \in S: m.ballot = k}
        V == {m.value: m \in maxmsgs}
    IN IF k = -1 THEN 
                    /\ \A m \in S: m.value = none
                    /\ v = any
               ELSE IF Cardinality(V) = 1 THEN
                       v \in V
               ELSE
                    \E CQ \in Quorums: Cardinality({m \in S: m.value = v}) >= Cardinality(CQ)
             
P2a(a, b) == /\ Select("p2a", b) = {}
             /\ b \in Fast
             /\ leader[a]
             /\ \E v \in Values \cup {any}:
                  \E Q \in Quorums:
                      /\ \A r \in Q: \E m \in SelectQuorum("p1b", b, Q): m.acceptor = r
                      /\ Safe(SelectQuorum("p1b", b, Q), v)
                      /\ Send([type |-> "p2a", ballot |-> b, value |-> v])
             /\ UNCHANGED <<maxBallot, votedBallot, votedValue, proposed, leader>> 
                         
P2b(a) == 
    \E m \in messages:
        \E v \in Values:
            /\ m.type = "p2a"
            /\ m.ballot >= maxBallot[a]
            /\ m.ballot > votedBallot[a]
            /\ \/ /\ m.value = any
                  /\ v \in proposed
               \/ m.value = v
            /\ Send([type |-> "p2b", ballot |-> m.ballot, voted |-> m.ballot, value |-> v, acceptor |-> a])
            /\ maxBallot' = [maxBallot EXCEPT ![a] = m.ballot]
            /\ votedBallot' = [votedBallot EXCEPT ![a] = m.ballot]
            /\ votedValue' = [votedValue EXCEPT ![a] = m.value]
            /\ UNCHANGED <<proposed, leader>>

(* 
wait for messages from fast quorum of acceptors in fast round
select safe value
if there are no safe values
select one from proposed set
*)            
CoordinatedRecovery(a, b) == 
    /\ leader[a]
    /\ b \in Fast
    /\ \E Q \in FastQuorums:
          \E v \in Values:
            /\ \A r \in Q: \E m \in SelectQuorum("p2b", b, Q): m.acceptor = r
            /\ Safe(SelectQuorum("p2b", b, Q), v)
            /\ Send([type |-> "p2a", ballot |-> b + 1, value |-> v])
    /\ UNCHANGED <<maxBallot, votedBallot, votedValue, proposed, leader>>   

Chosen(v) ==
    \E b \in Rounds:
       \E Q \in GetQuorums(b):
         \A a \in Q:
            \E m \in messages:
                /\ m.type = "p2b"
                /\ m.ballot = b
                /\ m.acceptor = a
                /\ m.value = v

Next == \/ \E a \in Acceptors:
            \/ P1b(a)
            \/ P2b(a)
            \/ \E b \in Fast:
                \/ P1a(a, b)
                \/ P2a(a, b)
                \/ CoordinatedRecovery(a, b)
        \/ \E v \in Values: Propose(v)
        \/ LeaderSelection

Spec == Init /\ [][Next]_vars

      
Consistency == \A v1, v2 \in Values: Chosen(v1) /\ Chosen(v2) => (v1 = v2)          
Liveness == []<>(Cardinality({v \in Values: Chosen(v)}) = 1)

=============================================================================
\* Modification History
\* Last modified Sat Apr 18 18:18:44 EEST 2020 by dd
\* Created Tue Apr 14 16:25:03 EEST 2020 by dd
