# Report 285: T10 datum basics

## 1. Theorems proved

The module proves the three requested API fields with the exact statements:

```lean
theorem datum_unique :
    ∀ (s : ℝ) (z : SpatialField) (A B : PeriodicSobolev s),
      IsPeriodicDatum s z A → IsPeriodicDatum s z B → A = B

theorem datum_real :
    ∀ (s : ℝ) (z : SpatialField) (A : PeriodicSobolev s),
      IsPeriodicDatum s z A →
        ∀ (i : Fin 3) (k : PeriodicFrequency), A.1 i (-k) = star (A.1 i k)

theorem meanZero_datum :
    ∀ (s : ℝ) (z : SpatialField) (A : PeriodicSobolev s),
      IsPeriodicDatum s z A →
        ∃ B : PeriodicSobolev s,
          IsPeriodicDatum s (meanZeroPartT z) B ∧ B ∈ meanZeroPeriodicSobolev s
```

It also proves the requested reusable
`IsPeriodicDatum.integrable_component`, plus the constant-mode, subtraction,
zero-coefficient/mean, and finite zero-mode lemmas used by the construction.

## 2. Files and Lean content

- `formalization/NSFormalization/Section3/T10/DatumBasics.lean`: implementation,
  auxiliary lemmas, and a concrete zero-field non-vacuity example.
- `research/T10/probes/datum_basics_closes.lean`: verbatim field-statement
  closure checks.
- `research/T10/axioms_datum_basics.lean`: transitive axiom audit for every
  named declaration.
- `research/T10/ATTEMPTS_DATUM_BASICS.md`: searches, failed routes, exact
  diagnostics, and their resolutions.
- `research/T10/REPORT_285.md`: this report.

The mean-zero datum is `A` minus its three scalar `lp.single` zero modes, so
membership in `lp 2` and the real submodule is obtained inside the existing
complete carrier rather than by rebuilding an arbitrary sequence.

## 3. Gaps

There are no residual named hypotheses and no mathematical or Lean proof
gaps.  The only significant elaboration obstacle was the private local Haar
`MeasureSpace` spelling described with exact errors in
`ATTEMPTS_DATUM_BASICS.md`; it was resolved by definitional conversion, with
no change to `PeriodicData.lean` and no weakening of any target.

## 4. Commands and results

Completed so far:

```text
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T10.DatumBasics
  success, 9353 jobs, 0 errors (only pre-existing replayed upstream warnings)

cd verification && lake env lean ../formalization/NSFormalization/Section3/T10/DatumBasics.lean
  success, 0 output

cd verification && lake env lean ../research/T10/probes/datum_basics_closes.lean
  success, 0 output

cd verification && lake env lean ../research/T10/axioms_datum_basics.lean
  success; every line reports exactly [propext, Classical.choice, Quot.sound]
```

```text
cd <worktree> && make check
  success, exit 0; plan, contract-policy (13 tests), and work-queue checks passed
```
