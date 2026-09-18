# REPORT — lane 341 (`341-T12-h2-linfty-laplacian-lambda`)

## 1. What was proved

Three fields of `MeanZeroSobolevCalculusAPI`
(`research/T12/probes/api_on_canonical.lean`), copied verbatim, with the API's
data fields `Cinfty` / `CHtwo` replaced by explicit positive constants.

* **`boundedRepresentative`** — the torus half of Lemma A.1,
  `appendix-a-local-theory.tex:12`:

      ∀ v : SpatialField, MemPeriodicHmVector 2 v →
        periodicLpENorm ⊤ v ≤ ENNReal.ofReal linftyConst * periodicSobolevENorm 2 v

  with `linftyConst = Real.sqrt (∑' k, (periodicFrequencyWeight k ^ 2)⁻¹)`,
  i.e. `Cinfty = (∑ₖ (1+4π²|k|²)^{-2})^{1/2}`, and `0 < linftyConst`
  (`linftyConst_pos`; in fact `1 ≤ linftyConst`).  No smoothness and no
  mean-zero hypothesis is added; the essential supremum is the one of the
  statement.

* **`hTwo_le_laplacian`** — the continuation comparison, `03-torus.tex:490-500`:

      ∀ v : SpatialField, SmoothPeriodicT v → IsMeanZeroT v →
        periodicSobolevENorm 2 v ≤ ENNReal.ofReal hTwoConst * periodicLpENorm 2 (laplacian v)

  with `hTwoConst = 1 + 1/(4π²)` and `0 < hTwoConst` (`hTwoConst_pos`).
  `laplacian` is the registered `Contracts/V1/GradientL6` spelling (the T12
  alias of `Section4.A05.lap`), not a Fourier multiplier.

* **`lambda_exists`** — `appendix-b-embeddings.tex:8-9,97`:

      ∀ v : SpatialField, SmoothPeriodicT v → ∃ Lv : SpatialField, IsPeriodicLambda v Lv

  The witness `lambdaField v` is built as the Fourier series with multiplier
  `2π|k| = sqrt(4π²|k|²)`; it is smooth, unit-periodic, real, and its
  coefficients are exactly the ones `IsPeriodicLambda` demands.

**No named input was introduced** and no statement was weakened.

## 2. What is in Lean now

New files only:

* `formalization/NSFormalization/Section3/T12/FourierEmbeddings.lean` (479
  lines, namespace `NSFormalization.Section3.T12`): §0 elementary weight facts
  (`fourierWeight_pos`, `fourierWeight_eq_one_add_angular`,
  `one_le_fourierWeight`, `fourierWeight_neg`, `angularFrequencySq_neg`,
  `four_pi_sq_le_angularFrequencySq`, `angularFrequencySq_pos`,
  `sqrt_angularFrequencySq_le_weight`, `reweightDatum_enorm_le'`); §1 the
  registered Laplacian spelling is smooth and periodic (`contDiff_laplacian`,
  `isPeriodicSpatial_laplacian`); §2 `hTwoConst`, `laplacianToWeight` and
  `hTwo_le_laplacian`; §3 `lambdaCoeff`, `lambdaField` and `lambda_exists`;
  §4 `linftyConst`, the reusable Fourier-series facts
  (`continuous_torusScalarSeries`, `norm_torusScalarSeries_le`,
  `ae_eq_torusScalarSeries` — `L²`-Fourier inversion a.e. through the
  `mFourierBasis` Hilbert basis) and `boundedRepresentative`.
  33 declarations, no `sorry` / `admit` / `axiom` / `native_decide`, no
  `maxHeartbeats` override needed.
* `research/T12/probes/fourier_embeddings_closes.lean`: each of the three
  fields (and the two positivity fields) closed by an `example` whose statement
  is the API field verbatim; plus a single-mode non-vacuity witness
  `modeField` (the real Fourier mode at `k = (1,0,0)`) with
  `modeField ≠ 0 ∧ SmoothPeriodicT modeField ∧ IsMeanZeroT modeField ∧
  MemPeriodicHmVector 2 modeField`, and `lambda_exists` applied to it.
* `research/T12/axioms_fourier_embeddings.lean`: `#print axioms` for all 33
  module declarations.
* `research/T12/ATTEMPTS_FOURIER_EMBEDDINGS.md` (reuse table, routes, dead
  ends with exact error text), this report, and a status line appended to
  `research/T12/COMPARISON.md` §1.

Reused, not re-proved: `T10/{ForcePaths,Parseval,DatumBasics,FourierCalculus}`,
`T11/MildPressure` (`torusScalarSeries` family, `summable_weight_pow_mul_coeff`,
`mildPressure_one_le_sq_sum`), `T12/SpectralGap` (`reweightDatum`).  See the
table in `ATTEMPTS_FOURIER_EMBEDDINGS.md`.

## 3. Gaps

* The lane's three targets have no residual obligation.
* Out of scope and still open in the API: `tameProduct`,
  `velocityCriticalL3`, `gradientLambdaCriticalL3`, `gradientLSix`.
  (`spectralGap` and `homogeneous_le_sobolev` are already proved in
  `Section3/T12/SpectralGap.lean`.)
* Neither constant is claimed sharp.  `CHtwo = 1 + 1/(4π²)` is the sharp
  unit-period constant for the mean-zero comparison; `Cinfty` is the
  Cauchy–Schwarz constant `‖W^{-1}‖_{ℓ²}`, larger than the optimal
  `H² → L^∞` constant.
* `RECONCILIATION.md` §4 item (11) — the *pointwise* `supNorm_le` half of
  `H² ↪ L^∞` that T18 will consume — is not added here; the field as reconciled
  is the essential-supremum one, and `ae_eq_torusScalarSeries` in this module is
  the piece a later lane needs for the pointwise version.
* `reweightDatum_enorm_le'` duplicates a `private` lemma of `SpectralGap`; a
  cleanup lane could de-privatise the original instead.

## 4. Commands run and results

From the worktree root, after `. scripts/lean-env.sh`:

* `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T12.FourierEmbeddings`
  → `Built NSFormalization.Section3.T12.FourierEmbeddings (3.0s)`,
  `Build completed successfully (9988 jobs)`, 0 errors.
* `cd verification && lake env lean ../formalization/NSFormalization/Section3/T12/FourierEmbeddings.lean`
  → no output (0 errors, 0 warnings).
* `cd verification && lake env lean ../research/T12/probes/fourier_embeddings_closes.lean`
  → only the 12 `#print axioms` lines, each
  `[propext, Classical.choice, Quot.sound]`; 0 errors, 0 warnings.
* `cd verification && lake env lean ../research/T12/axioms_fourier_embeddings.lean`
  → 33 lines, each `depends on axioms: [propext, Classical.choice, Quot.sound]`.
* `make check` → exit 0 (architecture checks, `test_contract_policy.py` 13
  tests OK, `check_work_queue.py` "45 work items: … consistent").

The worktree installer was run once first:
`LEAN_SEED_DIR=/data_8T/ping/blowup_density bash scripts/lean-install.sh` → `== OK`.
