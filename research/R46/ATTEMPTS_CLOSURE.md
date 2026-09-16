# Lane 259: completed homogeneous density and strong closure

## Successful route

`Bindings.CompletedClosure` proves both requested Spec fields with exactly one
named input, `NSFormalization.Section4.I03.CompactHomogeneousRealization`.
The theorem bodies were copied from Spec and compared byte for byte, including
the full three-norm sum and all five reference pins.

The homogeneous limit works for any `InsertionFamilyAPI`. On the eventually
smaller interval `(0, scalingThreshold A.scaling.correction]`, lane 250 gives
correction exponent `3/2` and source exponent `1/2`. Compact path measurability,
path uniqueness, and the Bochner triangle inequality identify and bound the
registered infimum. Continuity of the real powers and `ENNReal.ofReal` gives
the squeeze limit. No inhomogeneous-to-homogeneous embedding is used.

For strong closure, construct the packet, correction and family using the
caller's reference R itself. `InsertionLifespan.lifespan_eq` and
`sol_fullHorizon` provide the same exports used by the V2 record; both require
less than that record's extra `regularThrough` field. The energy convergence is
lane 249's `mainThresholds_energyConvergence`. The two Sobolev limits come from
the same family's `forceConvergence`, and addition yields the single sum.

For density, V2 B02 supplies a compact smooth approximant and a measurable
homogeneous path within `r/2`. The relative step uses lane 233's actual record L
when the approximant has lifespan greater than T, the homogeneous limit above,
and lane 252's compact closure. Extracting a measurable path from the infimum
and adding it to the first path gives a distance strictly less than r. The
`ENNReal.add_lt_add`/`add_halves` argument also handles an infinite radius.
Lane 256's requested file was absent at the initial `git show`, but appeared
later and its completed Sobolev proof was read before implementing this step.

## Rejected shortcuts and elaboration repairs

* Lane 233 selects another reference. Velocity uniqueness on a common slab
  does not give global equality of velocity fields, and cannot pin an arbitrary
  pressure gauge. Thus it cannot establish the raw Spec's full v/π equalities.
  Direct construction from R avoids this issue and needs no extra input. The
  density proof, which has no reference pins, does use lane 233 unchanged.
* An unrestricted homogeneous path-addition theorem is not supplied by the
  tree. The physical pairing uses totalized integrals. The new subtraction and
  addition lemmas require smooth compact physical fields, proving integrability
  against Schwartz tests before applying D01's subtraction theorem twice.
* `open NSFormalization.Section4 (D01 I03)` did not open those namespaces;
  elaboration reported `Unknown identifier I03.CompactHomogeneousRealization`.
  Opening `NSFormalization.Section4` fixes namespace resolution.
* Function zeros/lambdas prevented syntactic rewriting of the path-addition
  result. Explicit `change` to pointwise function algebra resolved the mismatch.
* `simpa only [hb] using hp` and the analogous limit transport reported a type
  mismatch between definitionally equal projections and constructed fields.
  Rewriting the exponent in the hypothesis and then `exact` avoids unnecessary
  simplifier transport. No unfolding of the large construction was needed.

## Fidelity and remaining scope

The Spec retains `forceSobolevENorm 1 0`; the reconciliation addendum proposes
`mixedLebesgueENorm 1 2`. They have different carrier definitions and are not a
reflexivity equality. This lane proves the literal Spec, without claiming a
new bridge or changing its spelling. The proposed literal mixed-norm variant
remains a separate vocabulary task.

No existing Lean module, binding, test, or contract was modified. The existing
COMPARISON document is updated under the task's explicit documentation request.
All Lean declarations use the default heartbeat limit. Both zero probes are
non-vacuous: the main file specializes completed density to b=0, a=0, ν=T=1;
the audit specializes the full simultaneous closure to the actual zero
classical reference, a=g=0, ν=T=δ=1.

## Validation

All commands sourced `scripts/lean-env.sh`; Lake ran in `verification/` with
`LEAN_NUM_THREADS=6`. Build and direct Lean check succeeded. The latter emitted
zero bytes; build output contains only existing dependency warning replays and
Lake status, not diagnostics from CompletedClosure. The audit printed exactly
`[propext, Classical.choice, Quot.sound]` for all nine named declarations and
accepted the zero-reference example. `make check`, `make test`,
`make test-mutations`, and `check_contracts.py --base-ref origin/erenup/integration`
all exited 0. For `make test`, a shell wrapper translated its fixed
`lake -d verification test` recipe into `cd verification; lake test` to obey the
working-directory restriction. Local command logs are in gitignored `tmp/closure-*`.
