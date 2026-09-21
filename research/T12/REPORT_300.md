# Lane 300 report — T12 spectral gap

## 1. Theorems and exact constants

The new module proves the two requested API fields:

```lean
theorem spectralGap :
    ∀ s : ℝ, 0 ≤ s → ∀ v : SpatialField,
      MemPeriodicHomogeneous s v →
        periodicSobolevENorm s v ≤
          ENNReal.ofReal (gapConst s) * periodicHomogeneousENorm s v

theorem homogeneous_le_sobolev :
    ∀ s : ℝ, 0 ≤ s → ∀ v : SpatialField,
      MemPeriodicHomogeneous s v →
        periodicHomogeneousENorm s v ≤ periodicSobolevENorm s v
```

Here the explicit constant and its required positivity are

```lean
def gapConst (s : ℝ) : ℝ :=
  (1 + 1 / (4 * Real.pi ^ 2)) ^ (s / 2)

theorem gapConst_pos (s : ℝ) (_hs : 0 ≤ s) : 0 < gapConst s
```

The reusable exports are the weight inequalities
`homogeneousDatumWeight_le_periodicFrequencyWeight_rpow` and
`periodicFrequencyWeight_rpow_le_gap_mul_homogeneous`, together with
`reweightDatum`, `reweightDatum_apply`, `reweightDatum_norm_le`, and
`reweightDatum_real`.

## 2. Files

- `formalization/NSFormalization/Section3/T12/SpectralGap.lean`: weight
  comparison, bounded nested-`lp` reweighting, datum transports, and both
  extended-norm theorems.
- `research/T12/probes/spectral_gap_closes.lean`: verbatim field-statement
  examples with `Cgap := gapConst`, positivity, and the full zero-field
  `MemPeriodicHomogeneous` guard.  Its Haar instances are explicitly named
  `spectralGapProbeUnitAddCircleMeasureSpace` and
  `spectralGapProbeUnitAddCircleProbability`.
- `research/T12/axioms_spectral_gap.lean`: all ten exported declarations print
  exactly `[propext, Classical.choice, Quot.sound]`.
- `research/T12/ATTEMPTS_SPECTRAL_GAP.md`: proof routes and exact resolved
  elaboration errors.
- `research/T12/REPORT_300.md`: this report.

## 3. Gaps and error text

No proof gaps or residual hypotheses remain.  The resolved error transcript is
recorded verbatim in `ATTEMPTS_SPECTRAL_GAP.md`.  The module imports
`DatumBasics` only, not `Parseval` or `PhysicalBridge`, so it avoids the known
pre-lane-296 instance-name collision.

## 4. Commands and results

- `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T12.SpectralGap`
  — PASS, 9360 jobs, 0 errors.  Lake replayed warnings from pre-existing
  dependencies only.
- `cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T12/SpectralGap.lean`
  — PASS, silent.
- `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T12/probes/spectral_gap_closes.lean`
  — PASS, silent.
- `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T12/axioms_spectral_gap.lean`
  — PASS; each of the ten declarations reports exactly
  `[propext, Classical.choice, Quot.sound]`.
- `make check` from the worktree root after `. scripts/lean-env.sh` — PASS,
  exit 0.  The existing formalization-plan report still prints
  `source_hashes_match: false` as informational output; all invoked checks and
  policy tests completed successfully.
