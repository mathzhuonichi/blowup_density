# Lane 287 report: periodic Leray projector

## 1. Theorems proved

The new module proves the exact API fields:

```lean
theorem leray_exists_contraction :
    ∀ (s : ℝ) (A : PeriodicSobolev s),
      ∃ B : PeriodicSobolev s,
        IsPeriodicLerayDatum A B ∧ ‖B‖ ≤ ‖A‖ ∧ IsSolenoidalPeriodicDatum B

theorem leray_projector :
    ∀ (s : ℝ) (A B C : PeriodicSobolev s),
      IsPeriodicLerayDatum A B → IsPeriodicLerayDatum B C → C = B
```

It also exports the requested fixed-point coefficient lemma:

```lean
theorem periodicLeray_of_solenoidal {s : ℝ} (A : PeriodicSobolev s) :
    IsSolenoidalPeriodicDatum A →
      ∀ (i : Fin 3) (k : PeriodicFrequency), periodicLeray s A i k = A.1 i k
```

## 2. Files and current Lean content

- `formalization/NSFormalization/Section3/T10/Leray.lean` realizes the symbol
  as a frequencywise orthogonal projection, constructs the output in `lp 2`,
  proves its reality and solenoidality, and establishes the exact norm bound.
- `research/T10/probes/leray_closes.lean` closes both requested API fields and
  the API's `leray_fixes_solenoidal` field.
- `research/T10/axioms_leray.lean` audits all three exported theorems.
- `research/T10/ATTEMPTS_LERAY.md` records the explored APIs and failed probes.

The module includes a concrete zero-datum non-vacuity example.

## 3. Gaps

There are no residual named hypotheses and no mathematical gaps.  The failed
probe diagnostics and their resolutions are recorded verbatim in
`ATTEMPTS_LERAY.md`.

## 4. Commands and results

- `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T10.Leray`
  — succeeded, 0 errors.
- `cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T10/Leray.lean`
  — succeeded with no output.
- `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T10/probes/leray_closes.lean`
  — succeeded with no output.
- `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T10/axioms_leray.lean`
  — each theorem printed exactly
  `[propext, Classical.choice, Quot.sound]`.
- `make check` from the worktree root — succeeded (exit code 0; all policy
  tests and work-queue checks passed).
