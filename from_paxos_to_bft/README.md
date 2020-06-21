From Paxos to BFT consensus protocol
===

Simplified, intuitive BFT protocol that is built on top classic single round Paxos
to tolerate byzantine failures.

## Classic Paxos

Paxos described in high detail in multiple sources. Below is a short description of the
protocol that should be enough to follow TLA+ specification.

Each server must maintain following non-volatile state:

- round. highest known round.
- voted round. highest round when server voted for a value.
- voted value. voted value in the voted round.

When server wants to LEARN a value it must increment `round` and send PREPARE
request to every other server. Every other server replies with PROMISE (starting from now
this server will be called coordinator, and any non-coordinator will be called acceptor). PROMISE must include `voted round` and `voted value`.

When coordinator receives PROMISEs from MAJORITY - Coordinator
will have enough information to proceed. Coordinator selects
a PROMISE with the highest `voted round` and picks `voted value` from this message.
If value is not defined then Coordinator is free to select ANY value, otherwise
original value must be selected.

Once value was selected, Coordinator prepares ACCEPT message and sends it to every
server. If round is atleast as high as server's round this value is accepted
(updated `voted round` and `voted value`). Server confirms that value was accepted
by sending ACCEPTED message.

Value is LEARNED by Coordinator if MAJORITY send ACCEPTED messages.

Safety of the protocol follows from the requirement that any two MAJORITIES must
intersect.

## Defining BFT protocol

BFT protocol will be defined by byzanting acceptor and coordinator
In first step Coordinator always acts according to protocol, and only acceptor
is byzantine. In second step Coordinator might be byzantine as well.

#### Byzantizing acceptors

###### Impersonating other acceptors

This is an obvious issue that needs to be addressed, byzantine server
may send replies on behalf of any other server. Addressed by adding
authenticators to messages (in practice using digital signatures).

In our model we will assume that any message from a server is authenticated. If message
are equal then we can aggregate authenticator and form certificate. Valid certificate
must have atleast MAJORITY authenticators.

###### Sending unsafe PROMISES

Byzantine server can trivially violate safety of the protocol by sending PROMISEs
for values that were never ACCEPTED.

It means that Coordiantor cannot assume that every received PROMISE is a valid one.
To ensure safety each value sent in PROMISE must carry a certificate.

Procol must be extended in a way to support certificates, for example:

1. Once MAJORITY of PROMISES were received, Coordinator sends PREACCEPT message
   to every server.
2. Server responds with PREACCEPTED message, this message must have an authenticator
   for PREACCEPTED value.
3. Coordinator aggregates PREACCEPTED messages from MAJORITY, forming certificate,
   and sends ACCEPT message.
4. Server updates `voted round` and `voted value` with certificate.

###### Forgetting ACCEPTED values

This is still not enough to make protocol safe. Byzantine acceptor may ignor
any local state and ACCEPT any proposed value. In such case different correct
Coordinators will LEARN different values.

To address this we need to revisit MAJORITY rule. Instead of requiring intersection
of any two MAJORITIES, we require that any intersection of MAJORITIES must have atleast one non-byzantine acceptor (quorum size is increased from 2f+1 to 3f+1).

#### Byzantizing coordinator

###### Invalid ACCEPT

First we handle trivial issue of invalid ACCEPT, from now before sending ACCEPTED
acceptor must validate that ACCEPT carries a certificate.

###### Invalid PREACCEPT

Byzantine coordinator may try to force acceptor to authenticate a random value.
As a an example, if MAJORITY accepted value A then by our assumption in Classic
Paxos section this value is safe and can be LEARNED. Valid coordinator will
wait for MAJORITY promises and hence won't PREACCEPT any other value.

Byzantine coordinator may try to PREACCEPT any random value, to protect against this
behavior acceptor will vote for value only if one of this condition is true:

- `voted value` is empty
- `voted value` is equal to the value in the PREACCEPT, technically valid PREACCEPT
  will also carry a valid certificate, but for this case this is unnecessary
- PREACCEPT certificate is formed in higher round than certificate of the `voted value`

However this "lock" introduces a liveness issue that will be addressed later.

###### Multiple PREACCEPTs per round

If coordinator forces acceptors to authenticate different messages in the same round, and "locks" enough acceptors with different values, so that no MAJORITY can't vote for the the same value - protocol will deadlock.

Example, acceptor A locked on X, B - Y. Acceptor C - none, D - byzantine. X and Y are equivalent
and neither A or B will be able to make progress.

To prevent voting multiple times in the same round acceptor will have an additiona variable
in the state:

- `auth round`. round when acceptor authenticated a value

Acceptor will respond only if PREACCEPT is from higher round than the `auth round`.

###### View/round synchronization

Byzantine leader may livelock the protocol by sending conflicting PREPARE. The same could happen
in non-byzantine consensus protocol, but it is usually avoided by introducing leases, such that
new coorinator will try to send PREPARE only if it didn't receive heartbeat message from
current coordinator recently.

Obviously we can't rely on hearbeats in BFT protocol and round synchronization must be changed so that
coordinator doesn't can't make a decision by himself to enter a new round or not.

In practice PROMISE now sent by every server eagerly when current coordinator is unresponsive (timeout), next coordinator aggregates PROMISEs and sends PREACCEPT message.

We will rename PROMISE to NEW-ROUND to be somewhat consistent with other protocols.

###### Locks and liveness

In section Invalid PREACCEPT additional locking constraints were introduced. With new locking
scheme we can't guarantee that leader will make progress in next round under certain
schedulling conditions. Example:

- `voted value` for acceptors A,B - empty. Acceptor C - X, Acceptor D - byzantine.
- Acceptor A,B,D - send a NEW-ROUND message to Acceptor A, since all of them are unlocked
  acceptor A will not learn latest message.
- Accept A - sends PREACCEPT with value Y. Acceptor D is byzantine and will not respond,
  acceptor B - replies with PREACCEPTED, acceptor C - doesn't reply, authenticating value Y
  is not safe according to rules specified in Invalid PREACCEPT section.

This scenario can repeat indefinitely in theory, in practice however it is likely that either A or B
will learn about X or C will become a coordinator. But it will definitely have negative impact
on protocol latency.

This problem is addressed is addressed in different ways in practical protocols:

- in pBFT acceptors must provide a proof to new coordinator that they didn't vote for higher value [pBFT. Castro & Liskov](http://pmg.csail.mit.edu/papers/osdi99.pdf)
- in Tendermint, next coordinator must wait a synchronous delay instead of waiting for MAJORITY of NEW-ROUND. In our example above, it will allow acceptor C to send X value. [Tendermint](https://arxiv.org/pdf/1807.04938.pdf)
- HotStuff introduces additional step in the protocol, such step guarantees that if any node got locked on a value, then MAJORITY know this value and will propagte in NEW-ROUND messages [HotStuff](https://arxiv.org/pdf/1803.05069.pdf)
