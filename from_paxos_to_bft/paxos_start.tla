---------------------------- MODULE paxos_start ----------------------------

EXTENDS Integers, FiniteSets

CONSTANTS Server, Value

Round == Nat

None == CHOOSE v : v \notin Value

prepare == "prepare"
promise == "promise"
accept == "accept"
accepted == "accepted"

VARIABLES msgs,
          round,
          votedValue,
          votedRound

vars == <<msgs,round,votedValue,votedRound>>

Send(msg) == msgs' = msgs \cup {msg}

Select(type,r) == {msg \in msgs: msg.type = type /\ msg.round = r}

SelectType(type) == {msg \in msgs: msg.type = type}

Quorum == {i \in SUBSET Server: Cardinality(i) * 2 > Cardinality(Server)}

SafeValue(v,S) == \E msg \in S: \A other \in S:
                     /\ msg.votedRound >= other.votedRound
                     /\ msg.votedValue = v

Init == /\ msgs = {}
        /\ round = [s \in Server |-> -1]
        /\ votedValue = [s \in Server |-> None]
        /\ votedRound = [s \in Server |-> -1]

PhasePrepare(r) == /\ Select(prepare, r) = {}
                   /\ Send([type |-> prepare, round |-> r])
                   /\ UNCHANGED <<round,votedValue,votedRound>>

PhasePromise(s) == \E msg \in SelectType(prepare):
                     /\ msg.round > round[s]
                     /\ Send([type |-> promise, round |-> msg.round, votedValue |-> votedValue[s],
                              votedRound |-> votedRound[s], server |-> s])
                     /\ round' = [round EXCEPT ![s] = msg.round]
                     /\ UNCHANGED <<votedValue,votedRound>>

PhaseAccept(r) == /\ Select(accept,r) = {}
                  /\ \E v \in Value: \E Q \in Quorum: \E S \in SUBSET Select(promise,r):
                     /\ \A s \in Q: \E msg \in S: msg.server = s
                     /\ \/ \A msg \in S: msg.votedValue = None
                        \/ SafeValue(v,S)
                     /\ Send([type |-> accept, round |-> r, value |-> v])
                     /\ UNCHANGED <<round,votedValue,votedRound>>

PhaseAccepted(s) == \E msg \in SelectType(accept):
                       /\ msg.round >= round[s]
                       /\ Send([type |-> accepted, round |-> msg.round, value |-> msg.value,
                                server |-> s])
                       /\ round' = [round EXCEPT ![s] = msg.round]
                       /\ votedRound' = [votedRound EXCEPT ![s] = msg.round]
                       /\ votedValue' = [votedValue EXCEPT ![s] = msg.value]

Next == \/ \E r \in Round:
          \/ PhasePrepare(r)
          \/ PhaseAccept(r)
        \/ \E s \in Server: \/ PhasePromise(s)
                            \/ PhaseAccepted(s)

Spec == Init /\ [][Next]_vars

Committed(v) == \E r \in Round:
                   \E Q \in Quorum:
                    \E S \in SUBSET Select(accepted,r):
                      /\ \A s \in Q: \E msg \in S:
                        /\ msg.server = s
                        /\ msg.value = v

Consistency == \A v1, v2 \in Value: Committed(v1) /\ Committed(v2) => v1 = v2
=============================================================================
\* Modification History
\* Last modified Mon Jun 22 15:58:16 EEST 2020 by dd
\* Created Mon Jun 22 15:06:22 EEST 2020 by dd
