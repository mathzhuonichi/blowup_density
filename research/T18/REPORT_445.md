# Lane 445 report — T18 U11 Sobolev rate and negative-order tail

## 1. Theorems and exact statements

All six U11 fields are proved in `NSFormalization.Section3.T18`, solely from
the `InsertionData` projections.  The chosen constant absorbs both lower-order
terms in the upstream T15/T17 estimates:

```lean
def forceDiffSobolevConst (data : InsertionData) (s : ℝ) : ℝ :=
  2 * (data.scaling.sobolevConst s + data.correction.sobolevConst s)

theorem forceDiffSobolevConst_pos (data : InsertionData) :
    ∀ s : ℝ, 0 ≤ s → s < 1 / 2 → 0 < forceDiffSobolevConst data s

theorem forceDifference_sobolev_memLp (data : InsertionData) :
    ∀ s : ℝ, 0 ≤ s → s < 1 / 2 → ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
      MemForceSobolevT 1 s (fun z ↦ force data ε z - data.g z)

theorem forceDifference_sobolev_bound (data : InsertionData) :
    ∀ s : ℝ, 0 ≤ s → s < 1 / 2 → ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
      forceSobolevENormT 1 s (fun z ↦ force data ε z - data.g z) ≤
        ENNReal.ofReal (forceDiffSobolevConst data s *
          (ε ^ ((1 : ℝ) / 2 - s) + ε ^ ((3 : ℝ) / 2 - s)))

theorem forceDifference_negativeSobolev_tendsto (data : InsertionData) :
    ∀ s : ℝ, s < 0 →
      Tendsto
        (fun ε : ℝ ↦ forceSobolevENormT 1 s
          (fun z ↦ force data ε z - data.g z))
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (0 : ℝ≥0∞))

theorem negative_s_memLp (data : InsertionData) :
    ∀ s : ℝ, s < 0 → ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
      MemForceSobolevT 1 s (fun z ↦ force data ε z - data.g z)
```

The module also proves the reusable infrastructure that the records do not
carry: integrable Fourier-coefficient additivity, `IsPeriodicDatum`/path
addition, evaluation of the path infimum by datum uniqueness, Minkowski for
`forceSobolevENormT`, contractivity of T11 `persistenceDown`, all-real-order
force-norm monotonicity, and lowering of honest `MemForceSobolevT` paths.

The positive rate uses `ε≤1` from `data.place.eps_le_one` and the two exact
record bounds.  For `s<0`, the order-lowering theorem gives
`forceSobolevENormT 1 s ≤ forceSobolevENormT 1 0`; the `s=0` U11 bound tends
to zero, so the squeeze theorem closes the requested limit.  The same lowering
map sends the honest order-zero path to an honest order-`s` path.

## 2. Files

- `formalization/NSFormalization/Section3/T18/SobolevRate.lean`: all six U11
  declarations plus nine supporting path-algebra/order-lowering declarations.
- `research/T18/probes/u11_closes.lean`: standalone exact Spec-form six-field
  structure, discharged through the U1 placement/cutoff/reference conversions
  and the registered Spec↔canonical bridges.
- `research/T18/axioms_u11.lean`: fifteen-declaration axiom audit.
- `research/T18/ATTEMPTS_U11.md`: proof route and every failed elaboration with
  its exact compiler text.
- `research/T18/T18_SPLIT.md`: U11 marked complete.
- `research/T18/REPORT_445.md`: this report.

## 3. Gaps and error text

There is no residual theorem, missing record fact, admission, named input, or
final compiler error.  In particular, the negative-order honesty field does
not require a new T15/T17 record field: their order-zero guards lower through
T11 `persistenceDown`.

The one requested source artifact absent on this base is lane 438's report;
the exact read error was:

```text
sed: can't read research/T17/REPORT_438.md: No such file or directory
```

This creates no proof gap because the checked-in T11 order-lowering machinery
is sufficient.  All resolved Lean failures are reproduced verbatim in
`ATTEMPTS_U11.md`.

## 4. Commands and results

All Lake commands ran from `verification/` after sourcing
`scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`.

| Command | Result |
|---|---|
| `lake build NSFormalization.Section3.T18.Insertion NSFormalization.Section3.T11.Persistence NSFormalization.Section3.T10.ForcePaths` | pass; dependency closure built |
| `lake build NSFormalization.Paper1.ScalingLimits NSFormalization.Section3.T11.Persistence` | pass; newly imported closure built |
| `lake build NSFormalization.Section3.T18.SobolevRate` | pass, `Build completed successfully (10019 jobs)`; replayed dependency warnings only |
| `lake env lean ../formalization/NSFormalization/Section3/T18/SobolevRate.lean` | pass, 0 output |
| `lake env lean ../research/T18/probes/u11_closes.lean` | pass, 0 output |
| `lake env lean ../research/T18/axioms_u11.lean` | pass; all 15 declarations print exactly `[propext, Classical.choice, Quot.sound]` |
| `make check` | pass; 13 policy tests and the 45-item work queue pass |
| `git diff --check` | pass, 0 output |
| forbidden-token grep over the three Lean deliverables | pass, 0 matches |

`make check` retains the repository's pre-existing copied-source admission and
`source_hashes_match=false` inventory, while exiting successfully.
