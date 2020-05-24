------------------------------ MODULE hotstuff ------------------------------

EXTENDS Integers, FiniteSets, TLC

\* Set of servers that follow the protocol
CONSTANT Servers

\* function to determine which server is byzantine
CONSTANT IsByzantine(_)

\* Set of values that can be chosen
CONSTANT Values

----

\* value with view
VARIABLE prepare, locked

\* view of the server
VARIABLE views

\* view of the server when vote was granted
VARIABLE voted

\* set of globally available messages (perfectly available network)
VARIABLE messages

certs == <<prepare, locked>>
vars == <<certs, views, voted, messages>>

None == CHOOSE v : v \notin Values

Views == Nat

TypeNewView == "new-view"
TypePrepare == "prepare"
TypePrepareResp == "prepare-resp"
TypePrecommit == "precommit"
TypePrecommitResp == "precommit-resp"
TypeCommit == "commit"
TypeCommitResp == "commit-resp"

VoteTypes == {TypeCommitResp, TypePrepareResp, TypePrecommitResp}
----

\* various helpers

PrintVal(id, exp) == Print(<<id, exp>>, TRUE)

PrintMessages(type) == /\ PrintVal("messages", {m \in messages: m.type = type})
                       /\ UNCHANGED <<vars>>

Quorum == {s \in SUBSET Servers: Cardinality(s) * 3 > Cardinality(Servers) * 2}

\* asserts that signatures are matching to any quorum
VerifyAuth(cert) == \E Q \in Quorum: \A s \in Q: s \in cert.auth

\* safe to vote only if we didn't vote in the same view
\* and
\* or locked is none
\* or locked is the proposed value
\* or there is exists a quorum that voted for another value in higher round
\* in last case it is safe because it means that value that we locked on wasn't commited
SafeToVote(s, msg) == \/ locked[s].value = None
                      \/ locked[s].value = msg.value
                      \/ /\ locked[s].value /= msg.value
                         /\ msg.cert.view > locked[s].view
                         /\ VerifyAuth(msg.cert)

Send(msg) == messages' = messages \cup {msg}

Messages(type, view) == {m \in messages: m.type = type /\ m.view = view}

MatchMessages(Q, type, view) == {m \in Messages(type, view): m.server \in Q}

MatchMessagesWithValue(Q, type, view, value) == {m \in MatchMessages(Q, type, view): m.value = value}

\* asserts message in msgs set if received from every server in quorum (Q)
AssertQuorum(Q, msgs) == \A s \in Q: \E m \in msgs: m.server = s

----

Init == /\ messages = {}
        /\ views   = [s \in Servers |-> 0]
        /\ voted   = [s \in Servers |-> 0]
        /\ prepare = [s \in Servers |-> [value |-> None, view |-> 0, auth |-> Servers]]
        /\ locked  = [s \in Servers |-> [value |-> None, view |-> 0, auth |-> Servers]]

----

\* for simplification next leader will always have to wait for quorum of NewView messages from previous round
\* in the model they can be emitted at any time, but protocol will make progress only if they are emitted after
\* server sent TypeCommitResp
\* we never send new-view for the last round
NewView(s, view) == /\ view > views[s]
                    /\ views' = [views EXCEPT ![s] = view]
                    /\ Send([type   |-> TypeNewView,
                             server |-> s,
                             view   |-> view-1,
                             cert   |-> prepare[s]])
                    /\ UNCHANGED <<certs, voted>>


\* aggregate NewView messages sent in the previous view, select the highest certificate with correct signatures
PrepareReq(l) == /\ Messages(TypePrepare, views[l]) = {}
                 /\ \E Q \in Quorum:
                       /\ AssertQuorum(Q, MatchMessages(Q, TypeNewView, views[l]-1))
                       /\ LET msgs == MatchMessages(Q, TypeNewView, views[l]-1)
                              highest == CHOOSE m \in msgs: /\ \A lower \in msgs: m.cert.view \geq lower.cert.view
                                                            /\ VerifyAuth(m.cert)
                          IN \E v \in Values:
                             /\ \/ highest.cert.value = None
                                \/ highest.cert.value = v
                             /\ Send([type   |-> TypePrepare,
                                      server |-> l,
                                      value  |-> v,
                                      view   |-> views[l],
                                      cert   |-> highest.cert])
                             /\ UNCHANGED <<views, certs, voted>>

\* vote for proposal if the server haven't voted in this round and proposal is safe
HandlePrepareReq(s) == \E msg \in messages:
                          /\ msg.type = TypePrepare
                          /\ msg.view = views[s]
                          /\ msg.view > voted[s]
                          /\ SafeToVote(s, msg)
                          /\ voted' = [voted EXCEPT ![s] = msg.view]
                          /\ Send([type   |-> TypePrepareResp,
                                   server |-> s,
                                   view   |-> msg.view,
                                   value  |-> msg.value])
                          /\ UNCHANGED <<views, certs>>

\* precommit and commit flows are identical
\* coordinator aggregates messages from previous round and makes a proposal with aggregated certificate
\* if certificate is valid - server will send a signature for the next step
PrecommitReq(l) == /\ Messages(TypePrecommit, views[l]) = {}
                   /\ \E v \in Values:
                       \E Q \in Quorum:
                         /\ AssertQuorum(Q, MatchMessagesWithValue(Q, TypePrepareResp, views[l], v))
                         /\ Send([type   |-> TypePrecommit,
                                  server |-> l,
                                  view   |-> views[l],
                                  cert   |-> [value |-> v, view |-> views[l], auth |-> {m.server: m \in MatchMessagesWithValue(Q, TypePrepareResp, views[l], v)}]])
                         /\ UNCHANGED <<views, certs, voted>>

HandlePrecommitReq(s) == \E msg \in messages:
                            /\ msg.type = TypePrecommit
                            /\ msg.view = views[s]
                            /\ VerifyAuth(msg.cert)
                            /\ prepare' = [prepare EXCEPT ![s] = msg.cert]
                            /\ Send([type   |-> TypePrecommitResp,
                                     server |-> s,
                                     view   |-> msg.view,
                                     value  |-> msg.cert.value])
                            /\ UNCHANGED <<views, locked, voted>>

CommitReq(l) ==  /\ Messages(TypeCommit, views[l]) = {}
                 /\ \E v \in Values:
                       \E Q \in Quorum:
                         /\ AssertQuorum(Q, MatchMessagesWithValue(Q, TypePrecommitResp, views[l], v))
                         /\ Send([type   |-> TypeCommit,
                                  server |-> l,
                                  view   |-> views[l],
                                  cert   |-> [value |-> v, view |-> views[l], auth |-> {m.server: m \in MatchMessagesWithValue(Q, TypePrecommitResp, views[l], v)}]])
                         /\ UNCHANGED <<views, certs, voted>>

HandleCommitReq(s) == \E msg \in messages:
                         /\ msg.type = TypeCommit
                         /\ msg.view = views[s]
                         /\ VerifyAuth(msg.cert)
                         /\ locked' = [locked EXCEPT ![s] = msg.cert]
                         /\ Send([type   |-> TypeCommitResp,
                                  server |-> s,
                                  view   |-> msg.view,
                                  value  |-> msg.cert.value])
                         /\ UNCHANGED <<views, prepare, voted>>



\* byzantine actions are limited only to double voting on any step
ActByzantine(s) ==  /\ IsByzantine(s)
                    /\ \E view \in Views: \E v \in Values: \E type \in VoteTypes:
                         /\ Send([type   |-> type,
                                  server |-> s,
                                  view   |-> view,
                                  value  |-> v])
                         /\ UNCHANGED <<views, voted, certs>>

Next == \/ \E s \in Servers:
           \/ \E view \in Views: NewView(s, view)
           \/ PrepareReq(s)
           \/ PrecommitReq(s)
           \/ CommitReq(s)
           \/ /\ ~IsByzantine(s)
              /\ \/ HandlePrepareReq(s)
                 \/ HandlePrecommitReq(s)
                 \/ HandleCommitReq(s)
           \/ ActByzantine(s)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* value is commited if there were TypeCommitResp messages from a quorum of servers
Commited(v) == \E view \in Views:
                  \E Q \in Quorum:
                     \A s \in Q:
                        \E m \in messages:
                          /\ m.type = TypeCommitResp
                          /\ m.view = view
                          /\ m.value = v
                          /\ m.server = s

Consistency == \A v1, v2 \in Values: Commited(v1) /\ Commited(v2) => (v1 = v2)
Termination == <>[](Cardinality({v \in Values: Commited(v)}) = 1)
=============================================================================
\* Modification History
\* Last modified Sun May 24 12:14:06 EEST 2020 by dd
\* Created Fri May 22 13:17:59 EEST 2020 by dd
