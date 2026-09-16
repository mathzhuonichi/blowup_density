# Lane 257 — R45 rapid class and Schwartz specialization

## 1. The theorem proved

This lane proves all Corollary 4.5 conclusions for the rapidly decaying class
`Y = forceClassRapid`, with the exact binder and conjunct order fixed by
`research/R45/Spec.lean`:

- `density_rapid`;
- `zeroIff_rapid` in both directions;
- `regularReference_rapid`;
- the verbatim `schwartzDensity` field.

It also assembles the complete guarded parametric `density` and `zeroIff`
fields for `Y = forceClassCompact ∨ Y = forceClassRapid` by case analysis,
using lane 252 for the compact cases.

## 2. What Lean now contains

`verification/Bindings/RapidClassDensity.lean` contains the six declarations
above.  The proofs reuse the R41 class facts without new supplier assumptions:
G2 embeds rapid forces into `F_R`, G3 preserves rapid decay after the compact
insertion correction, and G4 embeds Schwartz solenoidal data into
`initialClassR`.  The rider follows lane 254's route: a single R42 insertion
record gives exact lifespan, force and energy closeness, and history equality,
with uniqueness identifying the record's reference solution with the caller's
reference on `[0,T)`.

`research/R45/axioms_rapid_class.lean` audits all six declarations.  Each
prints exactly `[propext, Classical.choice, Quot.sound]`.  Its non-vacuity
examples instantiate `ν = T = 1`, `a = g = 0`, obtain an actual rapid-class
breakdown force, and apply the rider to the transported zero classical
solution.  `research/R45/ATTEMPTS_RAPID.md` records the successful and rejected
routes, and `research/R45/COMPARISON.md` records the new proof status.

## 3. Gaps and scope

No rapid-class mathematical field remains open, and no hypothesis was
isolated.  Lane 254's `CompactClassRider.lean` is not on this branch, so the
guarded parametric `regularReference` combination was intentionally left to
the registration lane, as requested.  No existing formalization module,
contract, binding, or test file was edited.

## 4. Commands and results

All Lean commands sourced `scripts/lean-env.sh`, used
`LEAN_NUM_THREADS=6`, and ran Lake from `verification/`.

- `lake build Bindings.RapidClassDensity` exited 0.  Lake replayed existing
  upstream linter warnings; the new target emitted no warning.
- `lake env lean Bindings/RapidClassDensity.lean` exited 0 with zero output.
- `lake env lean ../research/R45/axioms_rapid_class.lean` exited 0; every
  `#print axioms` line printed exactly the required three axioms, and all
  non-vacuity examples elaborated.
- `make check` exited 0.
- `make test` exited 0; all 32 registered contract suites passed.
- `git diff --check` exited 0.

No push, merge, or rebase was performed.

## Lead note (review 257, 2026-09-17)

The statements above about lane 254 being absent describe the branch **before** the integration merge `f6e879f`; after it, `Bindings/CompactClassRider.lean` (254, PR #247) is present. Only the final guarded `regularReference` assembly (`Or.elim` of 254/257) and the API registration remain — done in lane 262.
