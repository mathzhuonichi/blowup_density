# REPORT 447 — T15 U10 pressure normalization

## 1. Theorems proved (exact statements)

Module: `NSFormalization.Section3.T15.Pressure`, namespace
`NSFormalization.Section3.T15`.

The literal `ScalingAPI.pressureSlice_integrable` field is:

```lean
theorem pressureSlice_integrable
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hcarrier_compact : IsCompact K)
    (hpressure_support : ∀ t ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space ↦ p (t, x)) ⊆ K)
    (hpressure_smooth : ContDiffOn ℝ ∞ (zeroPastField p)
      (Iio (1 : ℝ) ×ˢ (univ : Set Space)))
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      ∀ t ∈ Ico (0 : ℝ) place.T,
        Integrable
          (torusLift
            (fun x ↦ periodizedScaledPressure p place.x₀ place.T ε (t, x)))
          periodicTorusMeasure
```

The exact gauge form consumed by `ClassicalSolutionT.pressure_gauge` is:

```lean
theorem pressure_gauge
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hcarrier_compact : IsCompact K)
    (hpressure_support : ∀ t ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space ↦ p (t, x)) ⊆ K)
    (hpressure_smooth : ContDiffOn ℝ ∞ (zeroPastField p)
      (Iio (1 : ℝ) ×ˢ (univ : Set Space)))
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      PressureGaugeT (Ico (0 : ℝ) place.T)
        (normalizedScaledPressure p place.x₀ place.T ε)
```

Three honest reusable lemmas support them:

```lean
theorem scaledPressure_slice_contDiff
    {p : PressureField} {x₀ : Space} {T ε t : ℝ}
    (hε : 0 < ε)
    (hp : ContDiffOn ℝ ∞ (zeroPastField p)
      (Iio (1 : ℝ) ×ˢ (univ : Set Space)))
    (ht : t < T) :
    ContDiff ℝ ∞ (fun x : Space ↦ scaledPressure p x₀ T ε (t, x))

theorem periodizedScaledPressure_slice_integrable
    {p : PressureField} {x₀ : Space} {T ε t : ℝ}
    (hsupp : tsupport (fun x : Space ↦ scaledPressure p x₀ T ε (t, x)) ⊆
      interior fundamentalCube)
    (hsmooth : ContDiff ℝ ∞ (fun x : Space ↦
      scaledPressure p x₀ T ε (t, x))) :
    Integrable
      (torusLift (fun x ↦ periodizedScaledPressure p x₀ T ε (t, x)))
      periodicTorusMeasure

theorem normalizePressureT_pressureGauge
    {I : Set ℝ} {q : SpaceTimeScalar}
    (hq : ∀ t ∈ I,
      Integrable (torusLift (fun x ↦ q (t, x))) periodicTorusMeasure) :
    PressureGaugeT I (normalizePressureT q)
```

The proof transports past-zero smoothness through the pressure rescaling,
uses placement support and the vendor locally finite periodizer to make every
raw periodized slice continuous, and obtains real Haar integrability through
the complex `MemLp` bridge.  The gauge then expands to `integral_sub` and
`integral_const`; probability normalization makes the constant integral equal
the subtracted mean.

All five declarations print exactly
`[propext, Classical.choice, Quot.sound]`.

## 2. Files delivered

- `formalization/NSFormalization/Section3/T15/Pressure.lean`: the five proved
  declarations above.
- `research/T15/probes/pressure_closes.lean`: literal field and gauge types
  closed by bare `exact`; full `[0,1)` gauge instantiated on the same bump
  pressure, cube centre, support ball, and placement geometry as
  `placement_closes.lean`.
- `research/T15/axioms_u10.lean`: axiom audit for every module declaration.
- `research/T15/ATTEMPTS_U10.md`: successful route and every failed approach
  with exact Lean error text.
- `research/T15/T15_SPLIT.md`: U10 status marked complete.
- `research/T15/REPORT_447.md`: this report.

## 3. Gaps and error text

No proof, statement, conformance, axiom, or gate gap remains.  Final module and
probe error text: none.

The main intermediate obstacle was that the T13 and vendor lattice vectors
are propositionally rather than definitionally identified.  Before adding
`latticeVector_eq_lattice`, Lean reported:

```text
Type mismatch: After simplification, term
  hslice
has type
  ContDiff ℝ ∞ fun x ↦ ∑' n,
    scaledPressure p place.x₀ place.T ε
      (t, x - NavierStokes.PeriodicLocalization.lattice n)
but is expected to have type
  ContDiff ℝ ∞ fun x ↦ ∑' n,
    scaledPressure p place.x₀ place.T ε (t, x - latticeVector n)
```

The complete verbatim diagnostics for this and all other rejected drafts are
in `research/T15/ATTEMPTS_U10.md`.

## 4. Commands and results

All `lake` commands were run from `verification/` after sourcing
`scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`.

- `lake build NSFormalization.Section3.T15.SingleCopy` — dependency closure
  built successfully, 0 errors.
- `lake build NSFormalization.Section3.T15.Pressure` — pass, 0 errors; only
  replayed upstream warnings appeared.
- `lake env lean ../formalization/NSFormalization/Section3/T15/Pressure.lean`
  — pass, 0 output.
- `lake env lean ../research/T15/probes/pressure_closes.lean` — pass, 0 output.
- `lake env lean ../research/T15/axioms_u10.lean` — pass; all five declarations
  print exactly `[propext, Classical.choice, Quot.sound]`.
- `rg` over all three delivered Lean files for
  `sorry|admit|axiom|native_decide|maxHeartbeats` — no matches.
- `git diff --check` — pass, 0 output.
- `make check` — pass: formalization-plan check, contract/import policy, 13
  policy tests, and the 45-work-item queue check all completed successfully.
