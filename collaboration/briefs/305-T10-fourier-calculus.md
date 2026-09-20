# Lane 305-T10-fourier-calculus — Fourier calculus on the unit torus for smooth periodic fields (derivative symbols, decay, inversion)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/305-T10-fourier-calculus` (git branch `erenup/305-T10-fourier-calculus`, based on `origin/erenup/integration-section3`: canonical modules
`formalization/NSFormalization/Section3/T10/PeriodicData.lean` (+ `PhysicalBridge`, `DatumBasics`, `Parseval`, `Leray` — all importable together since lane 296),
`Section3/T12/{MeanZeroCalculus,SpectralGap}.lean`, `Section3/T13/Localization.lean`). Read `CLAUDE.md`, `research/T10/COMPARISON.md` §"Needs a lemma" (items 2, 11, 12: the full-gradient
identity with the exact `2πk` factors; smooth periodic fields have coefficient paths at every order), `research/T12/COMPARISON.md` §"Proof dependencies" (what `boundedRepresentative`,
`lambda_exists`, `hTwo_le_laplacian`, `gradientLSix` need), `research/T13/COMPARISON.md` (same), the existing proof modules' reusable lemmas (`Section3/T10/DatumBasics.lean`:
`integral_mFourier`, `periodicFourierCoeff_const/sub`, `IsPeriodicDatum.integrable_component`; `Parseval.lean`: `fourier_repr_toLp`, `periodicFourierCoeff_real_neg`; `PhysicalBridge.lean`:
`periodic_shift_int`, `torusLift_apply_of_periodic`), `Paper1/TorusCube.lean` (`integral_torusLift`), and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. New files only; no edits to existing modules.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`; include non-vacuity `example`s (a single Fourier mode `x ↦ exp(2πi k·x)` and a constant).
- Before claiming a lemma is "not in the tree", `grep -rn` Mathlib's `Mathlib/Analysis/Fourier/AddCircleMulti.lean` (`mFourierCoeff_eq_integral`, `integral_preimage`, `measurePreserving_equivPiIoc`,
  `hasSum_mFourier_series_of_summable`, `hasSum_mFourier_series_apply_of_summable`, `mFourier_add/neg/zero/norm`), `Mathlib/Analysis/Fourier/AddCircle.lean` (1D: `has_antideriv_at_fourier_neg`,
  `fourierCoeff_eq_intervalIntegral`), `Mathlib/MeasureTheory/Integral/IntervalIntegral/*` (FTC: `intervalIntegral.integral_eq_sub_of_hasDerivAt`, integration by parts
  `intervalIntegral.integral_mul_deriv_eq_deriv_mul`), `Mathlib/MeasureTheory/Constructions/Pi.lean` (Fubini on `Fin 3 → ℝ`), and `Paper1/Periodic*.lean`, `Paper1/LocalizationBoundary.lean`.

## Goal — module `formalization/NSFormalization/Section3/T10/FourierCalculus.lean` (namespace `NSFormalization.Section3.T10`)
Work with scalar `f : Space → ℂ` (and `Space → ℝ` via coercion) that are `IsPeriodicSpatial` and `ContDiff ℝ ∞` (or `ContDiff ℝ n` with the needed `n`):
1. **Derivative symbol**: `periodicFourierCoeff_fderiv (hf : IsPeriodicSpatial f) (hs : ContDiff ℝ 1 f) (j : Fin 3) (k) :
   periodicFourierCoeff (fun x ↦ fderiv ℝ f x (coordinateVector j)) k = periodicDerivativeSymbol j k * periodicFourierCoeff f k`
   (`periodicDerivativeSymbol j k = 2πi k_j`). Route: `mFourierCoeff_eq_integral`/`integral_preimage` moves the Haar integral to the cube `∏ Ioc 0 1`; Fubini (`MeasureTheory.integral_prod`-style on
   `Fin 3 → ℝ` via `MeasurePreserving` of `MeasurableEquiv.piFinSuccAbove` or `Fin.insertNth`) isolates coordinate `j`; the 1D integration by parts on `[0,1]` has zero boundary term by
   periodicity (`f(x + e_j) = f x`, `mFourier` is 1-periodic in each coordinate). Iterate: `periodicFourierCoeff_iteratedFDeriv` for multi-indices / `∂_j^m` (at least `m ≤ 2` explicitly and the
   Laplacian: `periodicFourierCoeff (Δ f) k = -(4π²|k|²) · periodicFourierCoeff f k` with `Δ` spelled as `Section3/T12/MeanZeroCalculus.lean`'s `laplacian` on components / the scalar
   `scalarSpatialLaplacianT` of `Section3/T11` if present — say which and prove the identification).
2. **Decay**: `norm_periodicFourierCoeff_le`: `‖periodicFourierCoeff f k‖ ≤ ∫ ‖torusLift f‖` (trivial) and, from (1), `‖(2π k_j)^m periodicFourierCoeff f k‖ ≤ ∫ ‖torusLift (∂_j^m f)‖` for
   smooth periodic `f`; hence `(1 + 4π²|k|²)^N · ‖periodicFourierCoeff f k‖ ≤ C_N(f)` for every `N` (smooth periodic ⇒ rapidly decaying coefficients; use `Δ^N`).
3. **Summability and inversion**: `summable_periodicFourierCoeff_of_smooth` (from (2) with `N = 2` and `Summable (fun k : Fin 3 → ℤ ↦ (1 + |k|²)^(-2))` — prove or find the lattice summability
   in Mathlib (`summable_one_div_int_pow`-type per coordinate + products, or `Real.summable_abs_int_rpow`), and `periodic_eq_tsum_mFourier`: for continuous periodic `f` with summable coefficients,
   `f x = ∑' k, periodicFourierCoeff f k * exp(2πi k·x)` for all `x` (from `hasSum_mFourier_series_apply_of_summable` + `torusLift_apply_of_periodic`).
4. **Sup bound**: `norm_le_tsum_norm_periodicFourierCoeff`: `‖f x‖ ≤ ∑' k, ‖periodicFourierCoeff f k‖` (from (3)) — the pointwise half of `H² ↪ L^∞` that T12's `boundedRepresentative` needs
   once combined with Cauchy–Schwarz against the weight (state and prove that too: `∑' ‖f̂(k)‖ ≤ (∑' (1+4π²|k|²)^{-2})^{1/2} · (∑' (1+4π²|k|²)^2 ‖f̂(k)‖²)^{1/2}`).
Export everything with clear names; vector versions (componentwise, `SpatialField`) as corollaries.

## Deliverables
1. The module; conformance `research/T10/axioms_fourier_calculus.lean`; a probe `research/T10/probes/fourier_calculus_examples.lean` with the non-vacuity examples.
2. Records `research/T10/ATTEMPTS_FOURIER_CALCULUS.md` (paths tried, exact error text, any item you could not finish with its exact residual statement — finish the rest); report `research/T10/REPORT_305.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T10.FourierCalculus` (0 errors), `lake env lean` on the module, the probe and the axioms file, `make check` from the worktree root.

## Report
Commit on your branch (`[305-T10] FourierCalculus`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
