# REPORT 195 — interior momentum identity (review fix)

## 1. Result and exact interface

The lane remains intentionally conditional on `hprojected`; lane 197 owns the
projector bridge. The docstring now states honestly that this single equality
bundles both cylinder/Fourier projector identification and physical residual
agreement between the residual of the joint representative (using `f`) and the
descended cylinder residual (using `fc`). Lane 197 supplies the projector
comparison under decomposition inputs, lane 194 supplies the complement path
and a.e. residual bridge, and lane 192 supplies the canonical force/datum
wiring and solenoidality.

`interior_momentum_identity_of_complement_paths` is the new lane-194 adapter.
It takes the body of `exists_complement_paths` after its outer `w` witness, plus
the smooth representative and a.e. slices from
`exists_complement_joint_representative`. It selects the per-time datum by
`Classical.choose` and proves the same pointwise interior pressure-gradient
identity. Its `hprojected` input is projector identification on the selected
descended datum, while `hresidualAgreement` is the separate a.e. agreement of
lane 194's `residualSlice` with the physical residual. The lane-194 statement
is copied as a hypothesis because that branch cannot yet be imported here.

The lower-level `interior_momentum_identity_of_datums` now consumes the datum
of the smooth joint complement directly on interior slices. This is the exact
information produced by lane 194 after its a.e. slice transfer and avoids an
unnecessary globally selected `L²` complement path.

The compatibility export retains one bridge argument because lane 197's
verified `hprojected_of_cylinder` conclusion is exactly that composite
equality. The adapter can and does split the two halves because lane 194
explicitly names `residualSlice` before it is identified with the physical
residual.

## 2. Files

* `formalization/NSFormalization/Section4/A01/InteriorMomentum.lean` adds the
  locally-integrable datum uniqueness variant and the lane-194 adapter, and
  documents the full meaning and supplier chain of `hprojected`.
* `research/A01/axioms_interior_momentum.lean` audits the new declarations.
* `research/A01/probes/rev195_canonical_inputs.lean` checks lane 192's canonical
  `fc` and `u₀` at both assembly interfaces.
* `research/A01/probes/rev195_missing_bridge.lean` remains the expected negative
  example; `rev195_interval_mutation.lean` remains the expected endpoint failure.
* `research/A01/ATTEMPTS_INTERIOR_MOMENTUM.md` records the interface decisions.

No pre-existing formalization module was edited, and lane 194 was not copied or
imported wholesale.

## 3. Remaining boundary and negative diagnostics

This lane does not prove `hprojected`. Without it,
`rev195_missing_bridge.lean` fails with the unsolved goal equating the lowered
order-`m` cylinder residual datum to `A - lerayComplement 0 A`. This is the
intended negative example, not a claimed defect after the lead's scope decision.

The name `hprojected` must not be read as projector-only: independent `fc` and
`f` occur on its two sides. The assembly lane must use lane 192's canonical
force and datum and lane 194's physical residual selection when discharging
lane 197's decomposition hypotheses.

The interval mutation still fails because `0 ≤ t` at the left endpoint cannot
supply the strict inequality required by `Icc_mem_nhds`. Thus the ambient time
derivative conclusion remains restricted to `Ioo 0 S`.

## 4. Commands and results

All Lake commands ran from `verification/` after sourcing
`scripts/lean-env.sh` (as `../scripts/lean-env.sh` from that directory).

* `LEAN_NUM_THREADS=6 lake -q --log-level=error build
  NSFormalization.Section4.A01.InteriorMomentum` — PASS, zero output.
* `lake env lean
  ../formalization/NSFormalization/Section4/A01/InteriorMomentum.lean` — PASS,
  zero output.
* `lake env lean ../research/A01/axioms_interior_momentum.lean` — PASS; all ten
  declarations report exactly `[propext, Classical.choice, Quot.sound]`, and
  all three existing non-vacuity examples compile.
* `lake env lean ../research/A01/probes/rev195_canonical_inputs.lean` — PASS;
  both canonical partial applications elaborate and the solenoidal hypothesis
  is retained.
* `lake env lean ../research/A01/probes/rev195_missing_bridge.lean` — expected
  FAIL at line 48 with exactly the unsolved `hprojected` equality.
* `lake env lean ../research/A01/probes/rev195_interval_mutation.lean` —
  expected FAIL at line 26 because `ht.left : 0 ≤ t` cannot supply `0 < t` to
  `Icc_mem_nhds`.
* `make check` — PASS, including architecture, contract-policy, and work-queue
  checks.
* `git diff --check` — PASS.
