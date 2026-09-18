# Lane 321 report — T11 U10/U11 restart and selected local horizon

## 1. Theorems proved (exact statements)

The U10 theorem is the `PeriodicContinuationAPI.restart` field verbatim:

```lean
theorem restart (H : PeriodicQuantitativeLocalInput') :
    ∀ (ν : ℝ), 0 < ν →
    ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 ≤ S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ t₀ ∈ Icc (0 : ℝ) S,
            ∀ (a' : SpatialField), a' ∈ initialClassT →
              periodicSobolevENorm 1 a' ≤ K →
                ∃ w : ClassicalSolutionT ν a' (timeShiftT t₀ f) δ,
                  PeriodicLocalRegularity ν a' (timeShiftT t₀ f) δ w
```

The U11 partial assembly carries the first three fields verbatim:

```lean
horizon : ℝ → SpatialField → SpaceTimeField → ℝ

solution : ∀ (ν : ℝ), 0 < ν →
  ∀ (a : SpatialField), a ∈ initialClassT →
    ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ClassicalSolutionT ν a f (horizon ν a f)

regularity : ∀ (ν : ℝ) (hν : 0 < ν)
  (a : SpatialField) (ha : a ∈ initialClassT)
  (f : SpaceTimeField) (hf : f ∈ forceClassT),
    PeriodicLocalRegularity ν a f (horizon ν a f)
      (solution ν hν a ha f hf)
```

Supporting theorems prove
`forceSobolevENormT 1 s (timeShiftT t₀ f) ≤ forceSobolevENormT 1 s f`
for `0 ≤ t₀`, smoothness and periodicity of the shifted force, and
`timeShiftT 0 f = f`.

## 2. Files and resulting Lean API

- `formalization/NSFormalization/Section3/T11/Restart.lean` contains the
  shift estimate, exact `restart`, zero-time specialization, classical horizon
  choice with default `1` off the admissible class, selected solution,
  regularity, and `periodicLocalTheoryAPI_of_input` partial assembly.
- `research/T11/probes/restart_closes.lean` checks all four requested target
  shapes and the existing nonzero forced witness.
- `research/T11/axioms_restart.lean` guards every exported declaration and
  every declaration/projection of the partial structure at exactly
  `[propext, Classical.choice, Quot.sound]`.
- `research/T11/ATTEMPTS_RESTART.md` records the route, exact elaboration
  failures, and the sole named input.

## 3. Gaps and exact errors

No new gap was introduced.  All results are conditional only on the permitted
`PeriodicQuantitativeLocalInput'`, which U9d/U9e is assigned to discharge.
The five remaining full `PeriodicLocalTheoryAPI` fields belong to U5/U15/U16;
this lane deliberately packages only `horizon`, `solution`, and `regularity`.

The resolved dependent-transport error was:

```text
error: Tactic `rewrite` failed: motive is not type correct:
  fun _a => PeriodicLocalRegularity ν a f _a
    (periodicLocalSolutionOfInput H ν hν a ha f hf)
```

It was resolved by transporting a bundled solution/regularity subtype.  The
other exact resolved errors are recorded in `ATTEMPTS_RESTART.md`.

## 4. Commands and results

- `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.Restart`
  — passed (0 errors).
- `cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T11/Restart.lean`
  — passed (0 errors).
- `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T11/probes/restart_closes.lean`
  — passed (0 errors).
- `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T11/axioms_restart.lean`
  — passed (0 errors; all guarded declarations print exactly the standard three axioms).
- `make check` — passed (exit 0; plan, contract-policy, and work-queue checks all passed).
