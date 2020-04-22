------------------------------- MODULE Paxos -------------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Acceptors, Values

Quorums == {i \in SUBSET Acceptors: Cardinality(i) * 2 > Cardinality(Acceptors)}
Ballots == Nat

VARIABLES messages,
          maxBallot,
          votedBallot,
          votedValue

vars == <<messages, maxBallot, votedBallot, votedValue>>

Send(m) == messages' = messages \cup {m}
SelectMessages(t, b) == {m \in messages: m.type = t /\ m.ballot = b}

None == CHOOSE v: v \notin Values

Init == /\ messages = {}
        /\ maxBallot = [a \in Acceptors |-> -1]
        /\ votedBallot = [a \in Acceptors  |-> -1]
        /\ votedValue = [a \in Acceptors |-> None]

P1a(b) == /\ SelectMessages("p1a", b) = {}
          /\ Send([type |-> "p1a", ballot |-> b])
          /\ UNCHANGED <<maxBallot, votedBallot, votedValue>>

P1b(a) == \E m \in messages:
             /\ m.type = "p1a"
             /\ maxBallot[a] < m.ballot
             /\ Send([type |-> "p1b", 
                      ballot |-> m.ballot, 
                      acceptor |-> a, 
                      voted |-> votedBallot[a], 
                      value |-> votedValue[a]])
             /\ maxBallot' = [maxBallot EXCEPT ![a] = m.ballot]
             /\ UNCHANGED <<votedBallot, votedValue>>

(*
if quorum of acceptors responded
then pick value with the highest ballot
or pick any if there are no votes
*)             
P2a(b) == /\ SelectMessages("p2a", b) = {}
          /\ \E v \in Values:
             /\ \E Q \in Quorums:
                /\ \E S \in SUBSET SelectMessages("p1b", b):
                    /\ \A a \in Q: \E m \in S: m.acceptor = a
                    /\ \/ \E c \in 0..(b-1) : 
                          /\ \A m \in S : m.voted =< c
                          /\ \E m \in S : /\ m.voted = c
                                          /\ m.value = v
                       \/ \A m \in S: m.voted = -1 
             /\ Send([type |-> "p2a", ballot |-> b, value |-> v])
          /\ UNCHANGED <<maxBallot, votedBallot, votedValue>>

P2b(a) == \E m \in messages:
               /\ m.type = "p2a"
               /\ maxBallot[a] <= m.ballot
               /\ Send([type |-> "p2b", 
                          ballot |-> m.ballot, 
                          acceptor |-> a,
                          value |-> m.value])
               /\ votedBallot' = [votedBallot EXCEPT ![a] = m.ballot]
               /\ votedValue' = [votedValue EXCEPT ![a] = m.value]
               /\ maxBallot' = [maxBallot EXCEPT ![a] = m.ballot]

Next == \/ \E b \in Ballots:
           \/ P1a(b)
           \/ P2a(b)
        \/ \E a \in Acceptors:
           \/ P1b(a)
           \/ P2b(a)

Spec == Init /\ [][Next]_vars

Chosen(v) == \E b \in Ballots: 
                \E Q \in Quorums:
                   \A a \in Q: 
                      \E m \in messages:
                        /\ m.type = "p2b"
                        /\ m.ballot = b 
                        /\ m.acceptor = a 
                        /\ m.value = v
                        
Consistency == \A v1, v2 \in Values: Chosen(v1) /\ Chosen(v2) => (v1 = v2)
(*
requires stability of the leader to make progress
how it can be specified in tla?
*)
Finality == []<>(Cardinality({v \in Values: Chosen(v)}) = 1)

=============================================================================
\* Modification History
\* Last modified Sat Apr 18 17:52:39 EEST 2020 by dd
\* Created Mon Apr 13 15:36:20 EEST 2020 by dd
