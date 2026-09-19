# Lane 474 report — T21 N11, N13, N14, N15

## 1. Theorems and exact statements

All declarations are in `NSFormalization.Section3.T21`.

- `thresholdValue : T19.criticalOrder 1 = (1 : ℝ) / 2` (N11), by the
  canonical `T19.thresholdValue`.
- `zeroInitialClass : (fun _ : Space ↦ 0) ∈ initialClassT` (N12 transport),
  by `T20.zero_mem_initialClassT`.
- `fixedInitialDensity (D : T19.PeriodicDensityAPI)` (N13):

  ```lean
  ∀ a : SpatialField, a ∈ initialClassT →
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ s : ℝ, s < 1 / 2 →
        RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)
  ```

- `zeroInitialDensityIff D nonDensity` (N14):

  ```lean
  ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T → ∀ s : ℝ,
    RelativelyDenseT 1 s forceClassT
      (breakdownSetT ν (fun _ : Space ↦ 0) T) ↔ s < 1 / 2
  ```

  Its threaded `nonDensity` hypothesis is exactly the final
  `NonDensityAPI.nonDensity` field with `breakdownSetTZero` unfolded.  The
  forward direction applies `le_of_not_gt`; the backward direction specializes
  `D.fixedInitialDensity` at the proved zero datum.
- `zeroInitialNonDensity nonDensity` (N15):

  ```lean
  ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
    ∀ s : ℝ, 1 / 2 ≤ s →
      ¬ RelativelyDenseT 1 s forceClassT
        (breakdownSetT ν (fun _ : Space ↦ 0) T)
  ```

- `mainTheoremAPI D nonDensity : MainTheoremAPI` assembles the five intended
  fields (definitionally the verbatim fields after `breakdownSetTZero` unfolds).
  `mainOfDensityAndNonDensity_holds D nonDensity` exposes the same
  conditional assembly as a theorem.  The probe instantiates `D` with the
  canonical `T19.periodicDensityAPI`.

The source unfolds `breakdownSetTZero` deliberately: lane 472 is designated to own the
single canonical declaration in `Definitions.lean`.  Once both lanes are
present, its field type and these statements are definitionally equal.

## 2. Files

- `formalization/NSFormalization/Section3/T21/Main.lean`: canonical
  `MainTheoremAPI`, N11/N12/N13/N14/N15, and conditional assembly.
- `research/T21/probes/main_closes.lean`: each of the five fields and both
  package constructors checked with `exact`; the package uses
  `periodicDensityAPI`.
- `research/T21/axioms_n11_n15.lean`: transitive axiom audit for every authored
  declaration.
- `research/T21/ATTEMPTS_N11_N15.md`: exact failed elaboration and gate-race
  text plus the successful route.
- `research/T21/T21_SPLIT.md`: lane-474 status lines for N11--N15.
- `research/T21/REPORT_474.md`: this report.

## 3. Gaps and exact errors

There is no mathematical gap in N11 or N13--N15.  The only integration step
left to lane 475 is the promised adapter after lane 472's record is available:

```lean
fun _c D (N : NonDensityAPI _c) =>
  mainOfDensityAndNonDensity_holds D N.nonDensity
```

Thus this lane does not redeclare the parallel lane's `NonDensityAPI` or its
`mainOfDensityAndNonDensity : Prop`.  The exact residual registered statement is:

```lean
∀ c : ℝ, PeriodicDensityAPI → NonDensityAPI c → MainTheoremAPI
```

The first draft missed the namespace of `criticalOrder`; Lean reported:

```text
error: NSFormalization/Section3/T21/Main.lean:28:19: Function expected at
  criticalOrder
but this term has type
  ?m.1
```

Opening `NSFormalization.Section3.T19 (criticalOrder)` fixed it.  A later
parallel gate launch raced the rebuilding object and reported:

```text
error: object file '.../NSFormalization/Section3/T21/Main.olean' of module
NSFormalization.Section3.T21.Main does not exist
```

Sequential reruns passed.  Full exact text is in `ATTEMPTS_N11_N15.md`.

## 4. Commands and results

- `cd verification && LEAN_NUM_THREADS=6 lake build
  NSFormalization.Section3.T19.Assembly`: success, 10661 jobs.
- `cd verification && LEAN_NUM_THREADS=6 lake build
  NSFormalization.Section3.T21.Main`: success, 10724 jobs, 0 errors (replayed
  upstream warnings only).
- `cd verification && lake env lean
  ../formalization/NSFormalization/Section3/T21/Main.lean`: exit 0, no output.
- `cd verification && lake env lean
  ../research/T21/probes/main_closes.lean`: exit 0, no output.
- `cd verification && lake env lean
  ../research/T21/axioms_n11_n15.lean`: exit 0; every line printed exactly
  `[propext, Classical.choice, Quot.sound]`.
- `make check`: exit 0; 52 registered contracts and all policy/queue checks
  passed.
