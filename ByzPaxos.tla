------------------------------ MODULE ByzPaxos ------------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Values, Acceptors, ByzAcceptors

Ballots == Nat
AllAcceptors == Acceptors \cup ByzAcceptors
Quorums == {a \in SUBSET AllAcceptors: Cardinality(a) * 4 >= Cardinality(AllAcceptors)*3}

VARIABLES messages,
          maxBallot,
          votedBallot,
          votedValue,
          leader,
          received1b, \* all 1b messages received from acceptors. separate array to emulate independent delivery
          sent2av \* last 2av message for each value sent by an acceptor

consensus == <<maxBallot, votedBallot, votedValue>>
byzantine == <<received1b, sent2av>>
vars == <<messages, consensus, byzantine, leader>>

None == CHOOSE v: v \notin Values

Send(msg) == messages' = messages \cup {msg}
Select(type, ballot) == {m \in messages: m.type = type /\ m.ballot = ballot}

Init == /\ messages = {}
        /\ maxBallot = [a \in AllAcceptors |-> -1]
        /\ votedBallot = [a \in AllAcceptors |-> -1]
        /\ votedValue = [a \in AllAcceptors |-> None]
        /\ leader \in [AllAcceptors -> BOOLEAN]
        /\ received1b = [a \in AllAcceptors |-> {}]
        /\ sent2av = [a \in AllAcceptors |-> {}]
        

LeaderElection == /\ leader' \in [AllAcceptors -> BOOLEAN]
                  /\ UNCHANGED <<consensus, byzantine, messages>> 
        
Phase1a(a, b) == /\ Select("1a", b) = {}
                 /\ leader[a]
                 /\ Send([type |-> "1a", ballot |-> b])
                 /\ UNCHANGED <<consensus, byzantine, leader>>

Phase1b(a) == \E m \in messages:
                 /\ m.ballot > maxBallot[a]
                 /\ Send([type |-> "1b", 
                          ballot |-> m.ballot, 
                          voted |-> votedBallot[a], 
                          value |-> votedValue[a],
                          acceptor |-> a, 
                          2av |-> sent2av[a]])
                 /\ maxBallot' = [maxBallot EXCEPT ![a] = m.ballot]
                 /\ UNCHANGED <<votedBallot, votedValue, byzantine, leader>>

\* TODO enable async learning of 1b messages 
Learn1b(a) == /\ \E S \in SUBSET {m \in messages: m.type = "1b"}:
                  received1b' = [received1b EXCEPT ![a] = received1b[a] \cup S]
              /\ UNCHANGED <<messages, consensus, leader, sent2av>>

\* value that got majority of 1b messages in the highest round less than a current one
\* and one of the node in majority proposed this value must be selected
\* 2av is similar to a locked state in hotstuff/pbft
\* if less then f+1 nodes "locked" on a value protocol will be able to make progress
Safe(a, b, v) ==
    LET S == {m \in messages: m.type = "1b" /\ m.ballot = b}
    IN \/ \E Q \in Quorums:
            \A q \in Q: \E m \in S: /\ m.acceptor = q
                                    /\ m.voted = -1
                                    /\ m.value = None
       \/ \E c \in 0..b-1:
             \E Q \in Quorums:
                 /\ \A q \in Q: \E m \in S: /\ m.acceptor = q
                                            /\ m.voted =< c
                                            /\ (m.voted = c) => (m.value = v)
                 /\ \E m \in S: /\ m.acceptor \in Q
                                /\ \E r \in m.2av: /\ r.ballot >= c
                                                   /\ r.value = v            

\* non malicious leader can send 2a message only for the value it knows is safe
Phase2a(a, b) == /\ Select("2a", b) = {}
                 /\ leader[a]
                 /\ \E v \in Values:
                    /\ Safe(a, b, v)
                    /\ Send([type |-> "2a", ballot |-> b, value |-> v])
                    /\ UNCHANGED <<consensus, byzantine, leader>>
                    
Phase2av(a) == \E m \in messages:
                  /\ m.type = "2a"
                  /\ m.ballot >= maxBallot[a]
                  /\ \A 2av \in sent2av[a]: 2av.ballot # m.ballot \* same acceptor can't sign multiple votes in same ballot                    
                  /\ Safe(a, m.ballot, m.value)
                  /\ Send([type |-> "2av", acceptor |-> a, ballot |-> m.ballot, value |-> m.value])
                  /\ maxBallot' = [maxBallot EXCEPT ![a] = m.ballot]
                  /\ votedBallot' = [votedBallot EXCEPT ![a] = m.ballot]
                  /\ votedValue' = [votedValue EXCEPT ![a] = m.value]
                  /\ sent2av' = [sent2av EXCEPT ![a] = sent2av[a] \cup {[ballot |-> m.ballot, value |-> m.value]}]
                  /\ UNCHANGED <<leader, received1b>>

Phase2b(a) == \E v \in Values:
                \E b \in Ballots:
                    /\ \E Q \in Quorums:
                          \A q \in Q:
                            \E m \in messages:
                               /\ m.type = "2av"
                               /\ m.ballot = b
                               /\ m.value = v
                               /\ m.acceptor = q
                    /\ Send([type |-> "2b", value |-> v, ballot |-> b, acceptor |-> a])        
                    /\ UNCHANGED <<consensus, byzantine, leader>>

AcceptorNext == \E a \in Acceptors:
                   \/ \E b \in Ballots:
                      \/ Phase1a(a, b)
                      \/ Phase2a(a, b)
                   \/ Phase1b(a)
                   \/ Phase2b(a)
                   \/ Phase2av(a)

ByzAcceptorNext ==
        /\ \E a \in ByzAcceptors:
            \E b \in Ballots:
                \E v \in Values: \/ Send([type |-> "2av", ballot |-> b, value |-> v, acceptor |-> a])
                                 \/ Send([type |-> "2b", ballot |-> b, value |-> v, acceptor |-> a])
                                 \/ Send([type |-> "1b", ballot |-> b, voted |-> b, 
                                          value |-> v, acceptor |-> a, 2av |-> {}])
        /\ UNCHANGED <<consensus, byzantine, leader>>
                                      
Next == \/ AcceptorNext
        \/ LeaderElection
        \/ ByzAcceptorNext

Spec == Init /\ [][Next]_vars

Chosen(v) == 
    \E b \in Ballots:
       \E Q \in Quorums:
          \A a \in Q:
             \E m \in messages: /\ m.type = "2b"
                                /\ m.ballot = b
                                /\ m.acceptor = a
                                /\ m.value = v 
                                     
Consistency == \A v1, v2 \in Values: Chosen(v1) /\ Chosen(v2) => (v1 = v2)                                        
=============================================================================
\* Modification History
\* Last modified Thu Apr 23 14:43:36 EEST 2020 by dd
\* Created Tue Apr 21 16:44:40 EEST 2020 by dd
