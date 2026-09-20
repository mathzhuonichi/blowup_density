# T20 canonical H¹-ball check

Mechanical command (worktree root):

```text
grep -n "periodicSobolevENorm 1" research/T20/Spec.lean
```

It returns exactly two occurrences:

| Spec location | declaration/field | role | canonical proof dependency |
|---|---|---|---|
| `research/T20/Spec.lean:402` | copied T11 `PeriodicContinuationAPI.restart` | Uniform local restart for data in a finite H¹ ball. This is not a T20-specific definition or a field of `CriticalRegularityTAPI`. | Proving this manuscript field itself requires the named, unproved `NSFormalization.Section3.T11.PeriodicRestartH1`. The registered `PeriodicContinuationH3API.restart` is only the explicit H³ narrowing and does not prove this H¹ sentence. |
| `research/T20/Spec.lean:437` | copied T11 `PeriodicContinuationAPI.restartBeyond` | Uniform endpoint restart from an H¹ trajectory bound. This is likewise outside the T20-specific API. | Proving this manuscript field itself requires `PeriodicRestartBeyondH1` (which T11 documents as derivable from `PeriodicRestartH1`); the H³ field is not a silent substitute. |

## Consumer finding

`CriticalRegularityTAPI` has no local-theory, continuation, or mean-reduction
structure parameter. Its `continuationBound` directly records finiteness of the
squared-H² criterion, and `globalRegularity` directly records the proposition.
Thus neither H¹ occurrence above is consumed by the canonical T20 statement.

For a later proof of `globalRegularity` through the canonical T11 API,
`research/T11/H1_GAP.md` §3 gives the sufficient route:

1. use the ball-free `higherOrderBound` at `m = 3` when a uniform trajectory
   bound is needed;
2. use the proved H³ `restartBeyond` internally to obtain the ball-free
   `extendsBeyond` field; and
3. consume the ball-free `lifespanInfiniteOfLocallyFinite` criterion.

Therefore the proved `PeriodicContinuationH3API` suffices for T20's current
criterion route. `PeriodicRestartH1` is not a T20 proof obligation. If a future
implementation invokes the manuscript `restart` or `restartBeyond` field
directly from only an H¹/H² bound, that would reopen the owner-level gap; it
must not be discharged by silently changing order 1 to order 3.

No change to `research/T20/Spec.lean` is made.
