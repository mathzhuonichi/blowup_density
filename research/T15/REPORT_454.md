# REPORT 454 — T15 U11 `solution` assembly

## 1. Theorem proved, exact statement, and clause list

Module `NSFormalization.Section3.T15.Solution`, namespace
`NSFormalization.Section3.T15`, proves the literal `ScalingAPI.solution`
conclusion:

```lean
theorem solution
    {ν : ℝ} {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hcarrier_compact : IsCompact K)
    (hvelocity_support : ∀ t ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space => u (t, x)) ⊆ K)
    (hpressure_support : ∀ t ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space => p (t, x)) ⊆ K)
    (hforce_support : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (hforce_zero : ∀ t : ℝ, t ≤ 0 → ∀ x : Space, f (t, x) = 0)
    (hvelocity_extension_smooth : ContDiffOn ℝ ∞ (zeroPastField u)
      (Iio (1 : ℝ) ×ˢ (univ : Set Space)))
    (hpressure_extension_smooth : ContDiffOn ℝ ∞ (zeroPastField p)
      (Iio (1 : ℝ) ×ˢ (univ : Set Space)))
    (hequation : ∀ t : ℝ, t < 1 → ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν
        (zeroPastField u) (zeroPastField p) t x = zeroPastField f (t, x))
    (hdivergence : ∀ t : ℝ, t < 1 → ∀ x : Space,
      spatialDivergence (zeroPastField u) t x = 0)
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      ∃ S : ClassicalSolutionT ν (0 : SpatialField)
          (periodizedScaledForce f place.x₀ place.T ε) place.T,
        S.velocity = periodizedScaledVelocity u place.x₀ place.T ε ∧
          S.pressure = normalizedScaledPressure p place.x₀ place.T ε
```

The conclusion after the raw premises is verbatim the field at
`Scaling.lean:301-305`.  The theorem constructs `periodizedSolution`, whose
velocity and pressure are definitionally the two pinned fields.

The exact raw `scalingStatement` clause union used is:

1. `IsCompact K`;
2. velocity slice support in `K` on `[0,1)`;
3. pressure slice support in `K` on `[0,1)`;
4. `CompactPositiveTimeSupport f`;
5. force vanishing for `t ≤ 0`;
6. past-zero velocity smoothness on `Iio 1 ×ˢ univ`;
7. past-zero pressure smoothness on `Iio 1 ×ˢ univ`;
8. the past-zero momentum equation for every `t < 1`;
9. past-zero incompressibility for every `t < 1`.

No named input or other packet clause is used.  U8 supplies initial data,
divergence, and momentum; U9 supplies the Sobolev path and pressure-gradient
membership; U10 supplies the pressure gauge.  The new module proves the four
regularity/periodicity fields.  In particular, Haar normalization equals the
existing cube-mean normalization by `Paper1.integral_torusLift`, so
`PeriodicPressureNormalization.normalizedPressure_contDiffOn` gives joint
pressure smoothness through time zero.  The horizon proof uses
`place.eps_time` at `place.ε₀` and `place.eps_pos`.

All eight declarations in the module print exactly
`[propext, Classical.choice, Quot.sound]`.

## 2. Files delivered

- `formalization/NSFormalization/Section3/T15/Solution.lean`: five supporting
  smoothness/periodicity facts, the Haar/cube normalization bridge,
  `periodizedSolution`, and the literal `solution` theorem.
- `research/T15/probes/solution_closes.lean`: a bare-`exact` field check and
  the concrete registered viscosity-one packet/placement from
  `equation_closes.lean`.  It produces a pinned `ClassicalSolutionT` at
  `ε = place.ε₀` and proves that solution's velocity is nonzero at an
  interior spacetime point.
- `research/T15/axioms_u11.lean`: axiom audit for all eight declarations.
- `research/T15/ATTEMPTS_U11.md`: proof route and resolved diagnostics.
- `research/T15/T15_SPLIT.md`: U11 marked complete.
- `research/T15/REPORT_454.md`: this report.

No existing Lean module was edited.

## 3. Gaps and error text

No proof, statement, non-vacuity, axiom, or gate gap remains.  There is no
named input, placeholder, or forbidden proof primitive.

The first implementation build failed because the two Section 4 field aliases
were not opened:

```text
error: NSFormalization/Section3/T15/Solution.lean:30:23: Application type mismatch: The argument
  q
has type
  SpaceTimeScalar
but is expected to have type
  Section4.A02.SpaceTimeScalar
in the application
  normalizePressureT q

error: NSFormalization/Section3/T15/Solution.lean:120:26: failed to synthesize instance of type class
  OfNat SpatialField 0
```

Opening `Section4.A02 (SpatialField SpaceTimeScalar)` resolved it.  The first
probe run then exposed reversed names for two registered packet fields:

```text
../research/T15/probes/solution_closes.lean:135:57: error(lean.invalidField): Invalid field `extension_velocity_smooth`: The environment does not contain `BlowupDensity.Contracts.V1.PacketAPI.extension_velocity_smooth`
../research/T15/probes/solution_closes.lean:136:11: error(lean.invalidField): Invalid field `extension_pressure_smooth`: The environment does not contain `BlowupDensity.Contracts.V1.PacketAPI.extension_pressure_smooth`
```

Using `velocity_extension_smooth` and `pressure_extension_smooth` resolved the
probe.  Full diagnostics are retained in `ATTEMPTS_U11.md`.

## 4. Commands and results

The environment was sourced with `. scripts/lean-env.sh`; every Lake command
ran from `verification/` with `LEAN_NUM_THREADS=6`.

- Dependency closure:
  `lake build NSFormalization.Section3.T15.Equation NSFormalization.Section3.T15.SobolevPath NSFormalization.Section3.T15.Pressure NSFormalization.Paper1.PeriodicPressureNormalization Bindings.Packet`
  — pass, 0 errors.
- `lake build NSFormalization.Section3.T15.Solution` — pass, 0 errors; only
  replayed upstream warnings.
- `lake env lean ../formalization/NSFormalization/Section3/T15/Solution.lean`
  — pass, 0 output.
- `lake env lean ../research/T15/probes/solution_closes.lean` — pass, 0 output.
- `lake env lean ../research/T15/axioms_u11.lean` — pass; every declaration
  reports exactly the three standard axioms.
- `make check` — pass: formalization-plan and contract/import policy checks,
  all 13 policy tests, and the 45-item work queue check completed successfully.
- `git diff --check` — pass, 0 output.
