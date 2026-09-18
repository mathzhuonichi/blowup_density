# Lane 362 report — T15 U1 canonical bridges

## 1. Theorems with exact statements

`NSFormalization.Section3.T15.Bridges` defines the Spec rescalings
`scaledStartTime`, `scaledSourcePoint`, `scaledVelocity`, `scaledPressure`,
`scaledForce`, `alphaT`, `periodizedScaledVelocity`,
`periodizedScaledPressure`, `periodizedScaledForce`, and
`normalizedScaledPressure` over the canonical T10/T13 vocabulary.  Its exact
bridge theorems are:

* `scaledVelocity_eq_parabolicVelocity`, with right side
  `Source.parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField u)`;
* `scaledPressure_eq_parabolicPressure`, with right side
  `Source.parabolicPressure ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField p)`;
* `scaledForce_eq_parabolicForce`, with right side
  `Source.parabolicForce ε⁻¹ (T - ε ^ 2) x₀ f`;
* `alphaT_formula`, the exact `-3 + 3 / p.toReal + 2 / q.toReal` formula;
* `normalizedScaledPressure_formula`, the exact subtraction of
  `pressureMeanT` from the periodized pressure; and
* `periodize_eq_vendor`, the pointwise equality
  `T13.periodize f x =
  NavierStokes.PeriodicLocalization.periodize (fun z => f z.2) (t,x)`.

The two completed-density drift checks are promoted as
`completedDense_eq_via` and `completedDenseHomogeneous_eq_via` using the
canonical B01/D01 vocabulary.

## 2. Files

* `formalization/NSFormalization/Section3/T15/Bridges.lean`
* `research/T15/probes/api_on_canonical.lean`
* `research/T15/axioms_u1.lean`
* `research/T15/ATTEMPTS_U1.md`
* status updates in `research/T15/T15_SPLIT.md` and `research/T15/COMPARISON.md`

The probe copies the Spec's packet-specialized definitions token-for-token and
proves each equals the canonical definition by `rfl`.  It additionally checks
`Contracts.V1.scaledPacket`, `Contracts.V1.scaledPressure`,
`Contracts.V1.scaledForce`, and `Contracts.V1.alpha` against the module.

## 3. Gaps

This lane only supplies definitional infrastructure.  It does not construct a
`ScalingAPI` witness or prove U2--U15: support placement, lattice summability
and single-copy identities, Haar/Lebesgue and Parseval bridges, energy/mixed
identities, PDE transport, solution regularity, pressure gauge,
Sobolev/convergence bounds, or non-vacuity.  The alpha theorem is formula-
shaped in the canonical module because `Contracts.V1.alpha` has no separate
upstream object; the direct contract equality is retained in the probe.

## 4. Commands and results

* `. scripts/lean-env.sh && cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T15.Bridges` — passed (0 errors; only pre-existing replayed linter warnings).
* `cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T15/Bridges.lean` — passed.
* `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T15/probes/api_on_canonical.lean` — passed.
* `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T15/axioms_u1.lean` — passed; every listed declaration prints exactly `[propext, Classical.choice, Quot.sound]`.
* `make check` — passed (exit 0).  The repository reported its existing
  inventory notices (`BoundaryCorollary.lean` in the copied-source admission
  scan and `source_hashes_match: false`); contract-policy tests and work-queue
  checks passed.
