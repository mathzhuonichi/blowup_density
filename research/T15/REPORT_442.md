# REPORT 442 — T15 U6 `unboundedSpeed` and U7 `force_mem`

## 1. Theorems proved (exact statements)

Module `NSFormalization.Section3.T15.Blowup` proves the canonical U6 field:

```lean
theorem unboundedSpeed
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hcarrier_compact : IsCompact K)
    (hvelocity_support : ∀ t ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space => u (t, x)) ⊆ K)
    (hspeed : SpeedUnboundedAtOne u)
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      SpeedUnboundedAt place.T
        (periodizedScaledVelocity u place.x₀ place.T ε)
```

Module `NSFormalization.Section3.T15.ForceMem` proves one support helper and
the canonical U7 field:

```lean
theorem scaledForce_supportedInCube
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hforce_support : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u p f K) {ε : ℝ}
    (hε : ε ∈ Ioc (0 : ℝ) place.ε₀) :
    NavierStokes.PeriodicLocalization.SupportedInCube 1
      (scaledForce f place.x₀ place.T ε)

theorem force_mem
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hforce_smooth : ContDiff ℝ ∞ f)
    (hforce_support : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      MemForceT (periodizedScaledForce f place.x₀ place.T ε)
```

For U6, `speed_unbounded_at_target` transports the packet's source-time-one
witnesses to `place.T`.  A positive-threshold witness is nonzero, U2 places it
in the cube, and U3's `velocity_singleCopy` transfers it to the periodization.
For U7, `parabolicForce_smooth` and `parabolicForce_positive_support` transport
the raw force clauses; vendor local finiteness and lattice reindexing give
smoothness and periodicity; the compact time projection of the scaled support,
together with `time_support_periodize`, supplies the `MemForceT` witness.

Every new module declaration prints exactly
`[propext, Classical.choice, Quot.sound]`.

## 2. Files delivered

- `formalization/NSFormalization/Section3/T15/Blowup.lean`
- `formalization/NSFormalization/Section3/T15/ForceMem.lean`
- `research/T15/probes/blowup_force_mem_closes.lean`: two bare-`exact`
  canonical field checks and a concrete cube-centred placement.  Its compact
  bump velocity has amplitude `(1-t)⁻¹`, so its speed blow-up is genuine; both
  delivered fields fire at `ε=1/2`.
- `research/T15/axioms_u6_u7.lean`: audits all three new module declarations.
- `research/T15/ATTEMPTS_U6_U7.md`: successful routes and exact diagnostics for
  both failed intermediate probe checks.
- `research/T15/T15_SPLIT.md`: U6 and U7 marked complete.
- `research/T15/REPORT_442.md`: this report.

## 3. Gaps and error text

There is no residual proof, statement, conformance, axiom, or gate gap.  No
named input, placeholder, or repackaged goal was introduced.

The only substantive intermediate elaboration failure was in the concrete
probe (the proof modules themselves closed on their first checks):

```text
../research/T15/probes/blowup_force_mem_closes.lean:77:7: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  tsupport ↑bfmBump
in the target expression
  closure (Function.support bfmField) ⊆ closure (Function.support ↑bfmBump)

hsub : Function.support bfmField ⊆ Function.support ↑bfmBump
h : closure (Function.support bfmField) ⊆ closure (Function.support ↑bfmBump)
⊢ tsupport bfmField ⊆ Metric.closedBall 0 (1 / 4)
```

It was resolved by ascribing the intermediate as
`tsupport bfmField ⊆ tsupport (⇑bfmBump)` before rewriting.  The initial
pre-build missing-`.olean` diagnostic and the parser follow-ons from a missing
`open scoped ContDiff` are recorded verbatim in `ATTEMPTS_U6_U7.md`.

## 4. Commands and results

All Lake commands ran from `verification/` after sourcing
`scripts/lean-env.sh`; builds used `LEAN_NUM_THREADS=6`.

- `lake build NSFormalization.Section3.T15.Blowup NSFormalization.Section3.T15.ForceMem`
  — pass, 0 errors; only replayed upstream warnings.
- `lake env lean ../formalization/NSFormalization/Section3/T15/Blowup.lean`
  — pass, 0 output.
- `lake env lean ../formalization/NSFormalization/Section3/T15/ForceMem.lean`
  — pass, 0 output.
- `lake env lean ../research/T15/probes/blowup_force_mem_closes.lean`
  — pass, 0 output.
- `lake env lean ../research/T15/axioms_u6_u7.lean` — pass; all three lines
  report exactly `[propext, Classical.choice, Quot.sound]`.
- `make check` — pass: formalization-plan check, contract/import policy, all
  13 policy tests, and the 45-item work queue check completed successfully.
