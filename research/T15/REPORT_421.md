# REPORT 421 — T15 U3 lattice summability and single copy

## 1. Theorems proved (exact statements)

Module: `NSFormalization.Section3.T15.SingleCopy`, namespace
`NSFormalization.Section3.T15`.

The value-generic lattice core is:

```lean
theorem supportedInCube_of_tsupport_subset_interior
    {V : Type*} [NormedAddCommGroup V] {g : Space → V}
    (hsupp : tsupport g ⊆ interior fundamentalCube) :
    NavierStokes.PeriodicLocalization.SupportedInCube 1
      (fun z : SpaceTime => g z.2)

theorem summable_lattice_of_tsupport_subset_interior
    {V : Type*} [NormedAddCommGroup V] {g : Space → V}
    (hsupp : tsupport g ⊆ interior fundamentalCube) (x : Space) :
    Summable (fun n : PeriodicFrequency => g (x - latticeVector n))

theorem lattice_term_eq_zero_of_mem_cube
    {V : Type*} [Zero V] {g : Space → V}
    (hsupp : tsupport g ⊆ interior fundamentalCube)
    {x : Space} (hx : x ∈ fundamentalCube)
    {n : PeriodicFrequency} (hn : n ≠ 0) :
    g (x - latticeVector n) = 0

theorem tsum_eq_single_copy_of_mem_cube
    {V : Type*} [NormedAddCommGroup V] {g : Space → V}
    (hsupp : tsupport g ⊆ interior fundamentalCube)
    {x : Space} (hx : x ∈ fundamentalCube) :
    (∑' n : PeriodicFrequency, g (x - latticeVector n)) = g x
```

With shared implicit parameters
`{u f : VelocityField} {p : PressureField} {K : Set Space}`, the six canonical
field theorems are:

```lean
theorem velocity_summable
    (hcarrier_compact : IsCompact K)
    (hvelocity_support : ∀ t ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space => u (t, x)) ⊆ K)
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      ∀ t : ℝ, t < place.T → ∀ x : Space,
        Summable (fun n : PeriodicFrequency ↦
          scaledVelocity u place.x₀ place.T ε (t, x - latticeVector n))

theorem pressure_summable
    (hcarrier_compact : IsCompact K)
    (hpressure_support : ∀ t ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space => p (t, x)) ⊆ K)
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      ∀ t : ℝ, t < place.T → ∀ x : Space,
        Summable (fun n : PeriodicFrequency ↦
          scaledPressure p place.x₀ place.T ε (t, x - latticeVector n))

theorem force_summable
    (hforce_support : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      ∀ t : ℝ, ∀ x : Space,
        Summable (fun n : PeriodicFrequency ↦
          scaledForce f place.x₀ place.T ε (t, x - latticeVector n))

theorem velocity_singleCopy
    (hcarrier_compact : IsCompact K)
    (hvelocity_support : ∀ t ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space => u (t, x)) ⊆ K)
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      ∀ t : ℝ, t < place.T → ∀ x ∈ fundamentalCube,
        periodizedScaledVelocity u place.x₀ place.T ε (t, x) =
          scaledVelocity u place.x₀ place.T ε (t, x)

theorem pressure_singleCopy
    (hcarrier_compact : IsCompact K)
    (hpressure_support : ∀ t ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space => p (t, x)) ⊆ K)
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      ∀ t : ℝ, t < place.T → ∀ x ∈ fundamentalCube,
        periodizedScaledPressure p place.x₀ place.T ε (t, x) =
          scaledPressure p place.x₀ place.T ε (t, x)

theorem force_singleCopy
    (hforce_support : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      ∀ t : ℝ, ∀ x ∈ fundamentalCube,
        periodizedScaledForce f place.x₀ place.T ε (t, x) =
          scaledForce f place.x₀ place.T ε (t, x)
```

The result is the requested single-copy transport: lane 376 places every
slice strictly in `interior fundamentalCube`; the vendor locally finite
translate theorem proves summability at arbitrary `x`; on `fundamentalCube`,
the coordinate argument from T13 kills every `n ≠ 0` term.  No named input was
introduced.

## 2. Files delivered

- `formalization/NSFormalization/Section3/T15/SingleCopy.lean`: four generic
  lattice lemmas and the six canonical `ScalingAPI` fields.
- `research/T15/probes/single_copy_closes.lean`: six bare-`exact` field-type
  checks, a full concrete `PlacementData`, all six conclusions at
  `ε=1/2`, `t=7/8`, and a proof that the active velocity slice is nonzero.
- `research/T15/axioms_u3.lean`: axiom audit for all ten declarations.
- `research/T15/ATTEMPTS_U3.md`: proof route and rejected alternatives.
- `research/T15/T15_SPLIT.md`: U3 status updated to complete.
- `research/T15/REPORT_421.md`: this report.

## 3. Gaps / error text

No proof, statement, conformance, or gate gap remains.  Final module and probe
checks emitted no error text.  The force in the concrete geometry is zero, but
its `CompactPositiveTimeSupport` is proved rather than assumed; velocity is the
same nonzero bump as the placement probe and is explicitly nonzero at the
active test point.

## 4. Commands and results

All `lake` commands were run from `verification/` after
`. ../scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`.

- `lake build NSFormalization.Section3.T15.SingleCopy` — pass, 0 errors; the
  new module built cleanly (only replayed upstream warnings appeared).
- `lake env lean ../formalization/NSFormalization/Section3/T15/SingleCopy.lean`
  — pass, 0 output.
- `lake env lean ../research/T15/probes/single_copy_closes.lean` — pass, 0
  output.
- `lake env lean ../research/T15/axioms_u3.lean` — pass; all ten declarations
  print exactly `[propext, Classical.choice, Quot.sound]`.
- `make check` from the worktree root — pass: formalization-plan check,
  contract/import policy, 13 policy tests, and 45-work-item queue check all
  completed successfully.
