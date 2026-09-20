# REPORT 450 — T15 U9 Sobolev path and pressure gradient

## 1. Theorems with exact statements

Namespace `NSFormalization.Section3.T15`. These are the two requested
`ClassicalSolutionT` field types, with the concrete periodized velocity and
normalized pressure substituted. Only raw packet smoothness/support and
`PlacementData` are assumed.

```lean
theorem periodized_sobolev
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hext : ContDiffOn ℝ ∞ (zeroPastField u) (Iio (1 : ℝ) ×ˢ (univ : Set Space)))
    (hK : IsCompact K)
    (hu : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space => u (t, x)) ⊆ K)
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀, ∀ m : ℕ, ∃ G : ℝ → PeriodicSobolev (m : ℝ),
      ContinuousOn G (Ico (0 : ℝ) place.T) ∧
        ∀ t ∈ Ico (0 : ℝ) place.T,
          IsPeriodicDatum (m : ℝ)
            (fun x => periodizedScaledVelocity u place.x₀ place.T ε (t, x)) (G t)

theorem periodized_pressure_gradient
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hext : ContDiffOn ℝ ∞ (zeroPastField p) (Iio (1 : ℝ) ×ˢ (univ : Set Space)))
    (hK : IsCompact K)
    (hp : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space => p (t, x)) ⊆ K)
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀, ∀ t ∈ Ico (0 : ℝ) place.T,
      MemLp (torusLift (fun x => pressureGradient
        (normalizedScaledPressure p place.x₀ place.T ε) t x)) 2 periodicTorusMeasure
```

The generic `contDiffOn_periodize_of_slice_support` proves joint slab
smoothness using a zero extension outside the slab and the vendor's locally
finite periodization theorem. `periodizedVelocity_contDiffOn` applies it to
the rescaled velocity. T11 supplies the datum at every integer order and
continuity on the full half-open interval, including time zero. Pressure
normalization subtracts a spatial constant on each smooth slice.

## 2. Files

- `formalization/NSFormalization/Section3/T15/SobolevPath.lean`: four theorems.
- `research/T15/probes/sobolev_path_closes.lean`: standalone copy of the exact
  lane-439 bump packet/placement geometry, both fields at `ε = 1/2`, every
  integer order, and explicit nonzero velocity and pressure checks.
- `research/T15/axioms_u9.lean`: all four module declarations audited.
- `research/T15/ATTEMPTS_U9.md`: each failed attempt with exact diagnostics.
- `research/T15/T15_SPLIT.md`: U9 completion status.
- `research/T15/REPORT_450.md`: this report.

No existing Lean module was edited. No push, merge, or rebase.

## 3. Gaps with error text

No residual mathematical statement or gate gap. Final Lean checks have no
errors or warnings. Development errors and their complete text are retained
in `ATTEMPTS_U9.md`: conditional membership simplification, elaboration of
normalization's constant slice, refolding `tsupport`, and evaluating bump
values without premature arithmetic simplification. All are resolved.

## 4. Commands and results

Environment sourced with `. scripts/lean-env.sh`; every `lake` command ran
from `verification/` with `LEAN_NUM_THREADS=6`.

- Dependency closure: `lake build NSFormalization.Section3.T15.Energy NSFormalization.Section3.T11.Maximal` — exit 0.
- `lake build NSFormalization.Section3.T15.SobolevPath` — exit 0, 10009 jobs, zero errors (upstream warnings replayed).
- `lake env lean ../formalization/NSFormalization/Section3/T15/SobolevPath.lean` — exit 0, zero output.
- `lake env lean ../research/T15/probes/sobolev_path_closes.lean` — exit 0, zero output.
- `lake env lean ../research/T15/axioms_u9.lean` — exit 0; all four print exactly `[propext, Classical.choice, Quot.sound]`.
- `make check` — exit 0, 13 policy tests pass, 45 work items consistent.
- `make test` — exit 0, through job 10911/10911; registered contracts pass.
- `make test-mutations` — exit 0, mutation suite passed.
