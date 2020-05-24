TLA+ model for hotstuff
===

Model reduces state space to the single height, if for original protocol safety and liveness condition would be expressed someting like:

```tla
SafeToVote(msg): msg.parent = locked.id \/ msg.cert.number > locked.number
```

Then for single height it will be simplified down to:

```tla
SafeToVote(msg): locked.value = None \/ msg.cert.number > locked.number
```

Assumptions
===

Only one Prepare/Preccomit/Commit messages are allowed per view, this assumes that the
leader is deterministically chosen for the given view and known to all replicas.

NewView messages are emmitted for any view but last, it guarantess that for any chain of executions
Termination temporal property will hold.

Termination expressed as:

```tla
Commited(v) == \E view \in Views:
                  \E Q \in Quorum:
                     \A s \in Q:
                        \E m \in messages:
                          /\ m.type = TypeCommitResp
                          /\ m.view = view
                          /\ m.value = v
                          /\ m.server = s

Termination == <>[](Cardinality({v \in Values: Commited(v)}) = 1)
```

Which in english means that eventually one value will be commited and will remain commited.

Byzantine actors
===

Protocol designed with the goal to support certain number of byzantine nodes.
There is a `IsByzantine` function to express this in the model.

Byzantine actor will ignore protocol and vote for every value in every view on the every step.
For 4 servers protocol must preserve Termination and Consistency properties with 1 byzantine actor.

```tla
Consistency == \A v1, v2 \in Values: Commited(v1) /\ Commited(v2) => (v1 = v2)
```