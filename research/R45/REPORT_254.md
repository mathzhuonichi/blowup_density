# Lane 254 — R45 compact regular-reference rider

## 1. The theorem proved

This lane proves `regularReference_compact`, the exact
`Y = forceClassCompact` specialization of the reconciled Corollary 4.5 field
`RClassesAPI.regularReference` in `research/R45/Spec.lean`.  For every regular
compact-force reference through `T+δ`, every cutoff `0 ≤ τ < T`, and every
positive force and energy radius, it produces one compact force and one
classical solution with exact maximal lifespan `T`, both strict approximation
bounds, and pointwise common velocity history on `[0,τ]`.

The lane also proves the requested cheap companion
`regularReference_of_memForceR`, the same epsilon-form statement with
`Y = forceClassR`.

## 2. What Lean now contains

`verification/Bindings/CompactClassRider.lean` contains both theorems.  The
compact proof makes one call to lane 233's `insertionLifespanV2_of_data` and
reuses lane 249's uniqueness, energy-congruence, energy-convergence, and force-
convergence route.  It chooses a single insertion scale satisfying the two
requested norm bounds and
`ε ≤ min 1 ((T-τ)/4)`.  The latter gives `τ ≤ T-2ε²`, so R42's registered
history covers the arbitrary Spec cutoff.  Its registered compact force
difference, together with lane 252's compact addition lemma, keeps the force
in `F_c`.

The ambient `F_R` theorem derives the epsilon form from Theorem 4.1's
Tendsto-shaped family rider, using `ε ≤ ε₀/2` for its strict scale interval.
`research/R45/axioms_compact_rider.lean` audits both theorem declarations and
contains a concrete non-vacuity application at `ν = T = 1`, `a = g = 0` using
the genuine zero solution on `[0,2)`.

Both theorem declarations report exactly
`[propext, Classical.choice, Quot.sound]`.

## 3. Gaps and scope

No compact-rider hypothesis or proof gap remains.  The rapid-class instances
of `density`, `zeroIff`, and `regularReference`, together with
`schwartzDensity`, remain outside this lane.  No existing Lean module,
contract, or test was edited; the only existing file changed is the requested
research comparison note.

## 4. Commands and results

All Lean commands sourced `scripts/lean-env.sh`, used
`LEAN_NUM_THREADS=6`, and ran Lake from `verification/`.

- `lake build Bindings.CompactClassRider` exited 0.  Lake replayed existing
  upstream linter warnings; the new target emitted no warning.
- `lake env lean Bindings/CompactClassRider.lean` exited 0 with no output.
- `lake env lean ../research/R45/axioms_compact_rider.lean` exited 0; both
  `#print axioms` lines printed exactly the required three axioms and the
  concrete non-vacuity example elaborated.
- `make check` exited 0.
- `make test` exited 0; all 32 registered contract suites passed.
- `git diff --check` exited 0.

No push, merge, or rebase was performed.
