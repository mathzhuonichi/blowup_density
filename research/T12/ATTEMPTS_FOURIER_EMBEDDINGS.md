# ATTEMPTS — lane 341 (`Section3/T12/FourierEmbeddings.lean`)

Targets: `boundedRepresentative`, `hTwo_le_laplacian`, `lambda_exists` of
`MeanZeroSobolevCalculusAPI` (`research/T12/probes/api_on_canonical.lean`).
All three are proved with explicit constants; **no named input was introduced**
and no statement was weakened.

## What was already in the tree (found by `grep`, not re-proved)

Searching `Section3/`, `Paper1/Periodic*.lean`, `Section4/{A02,A05}` before
writing anything turned up almost the whole toolbox, so the lane is mostly
assembly:

| needed | found |
|---|---|
| datum of a smooth periodic field at any order | `T10/ForcePaths.smooth_periodic_datum` |
| `periodicSobolevENorm s v = ‖A‖ₑ` (datum uniqueness) | `T10/ForcePaths.periodicSobolevENorm_eq` |
| `MemLp (torusLift v) q` for continuous `v` | `T10/ForcePaths.memLp_torusLift_vector`, `Paper1.memLp_torusLift` |
| Fourier symbol of the **registered** `laplacian` spelling | `T10/ForcePaths.periodicFourierCoeff_vector_laplacian` |
| vector Parseval `‖A‖ₑ = eLpNorm (torusLift v) 2` at order 0 | `T10/Parseval.parseval_forward` |
| `repr` of the Hilbert basis = `periodicFourierCoeff` | `T10/Parseval.fourier_repr_toLp` |
| `v̂(0) = mean` | `T10/DatumBasics.periodicFourierCoeff_zero_eq_mean_component` |
| conjugate reflection `v̂(-k) = star v̂(k)` | `T10/Parseval.periodicFourierCoeff_real_neg` |
| `∑ₖ W(k)^{-2} < ∞` and the `ℓ² → ℓ¹` Cauchy–Schwarz bound | `T10/FourierCalculus.summable_inverse_periodicFrequencyWeight`, `.tsum_norm_periodicFourierCoeff_le` |
| all-order weighted `ℓ¹` decay of smooth coefficients | `T11/MildPressure.summable_weight_pow_mul_coeff` |
| smooth / periodic / real / coefficient-inverting Fourier series | `T11/MildPressure.torusScalarSeries{,_contDiff,_periodic,_conj,_coeff}` |
| bounded diagonal reweighting of the `PiLp`/`lp` datum carrier | `T12/SpectralGap.reweightDatum{,_apply,_real,_norm_le}` |
| `1 ≤ ∑ⱼ kⱼ²` for `k ≠ 0` | `T11/MildPressure.mildPressure_one_le_sq_sum` |

Only `reweightDatum_enorm_le` had to be restated (`reweightDatum_enorm_le'`):
the `SpectralGap` copy is `private`.  The same is true of `SpectralGap`'s
`periodicFrequencyWeight_pos`, `one_le_frequency_sq_sum`,
`periodicAngularFrequencySq_pos`; §0 of the new module re-proves the four
one-liners rather than de-privatising another module.

## Routes taken

### `hTwo_le_laplacian` (`CHtwo = 1 + 1/(4π²)`)
Coefficientwise, no analysis.  Take the order-zero datum `B` of `Δv`
(`smooth_periodic_datum`), then `A := reweightDatum laplacianToWeight … B`
with

    laplacianToWeight k = if k = 0 then 0 else -(W k / (4π²|k|²)).

`|laplacianToWeight k| ≤ 1 + 1/(4π²)` because `4π²|k|² ≥ 4π²` off the zero
mode; the multiplier is even, so `reweightDatum_real` keeps the datum in the
conjugate-reflection subspace.  `A` *is* the order-two datum of `v`: at `k ≠ 0`
the two sign flips cancel, and at `k = 0` the physical `IsMeanZeroT v` plus
`periodicFourierCoeff_zero_eq_mean_component` makes both sides `0` — this is
exactly where the mean-zero hypothesis is used, and without it the field is
false (`v ≡ c ≠ 0`).  Then
`periodicSobolevENorm 2 v ≤ ‖A‖ₑ ≤ ofReal CHtwo * ‖B‖ₑ = ofReal CHtwo * ‖Δv‖_{L²}`
by `parseval_forward`.

### `lambda_exists`
`lambdaCoeff v i k = sqrt(4π²|k|²) · v̂ᵢ(k)`, and
`Lv x = toSpace (fun i ↦ (torusScalarSeries (lambdaCoeff v i) x).re)`.
Smoothness comes from `torusScalarSeries_contDiff`, whose hypothesis
`∀ N, Summable (W^N ‖c‖)` follows from `summable_weight_pow_mul_coeff` at order
`N+1` together with `sqrt(4π²|k|²) ≤ W k` (proved via `a ≤ (1+a)²`).
Reality is `torusScalarSeries_conj` applied to `lambdaCoeff v i (-k) = star (lambdaCoeff v i k)`,
and the coefficient clause is `torusScalarSeries_coeff` plus `Complex.conj_eq_iff_re`.

### `boundedRepresentative` (`Cinfty = (∑ₖ W(k)^{-2})^{1/2}`)
The hypothesis is only `MemPeriodicHmVector 2 v`, i.e. **no smoothness**, so the
inversion has to be the `L²` one.  Steps:

1. `periodicSobolevENorm 2 v ≠ ⊤` gives a datum `A` (empty `iInf` is `⊤`), and
   `A i k = W k · v̂ᵢ(k)` after `Real.rpow_one`.
2. `lp.hasSum_norm` gives `∑ₖ ‖A i k‖² = ‖A i‖²`, hence the hypothesis of
   `tsum_norm_periodicFourierCoeff_le`, hence
   `∑ₖ ‖v̂ᵢ(k)‖ ≤ Cinfty ‖A i‖`.  Absolute summability itself is the AM–GM
   bound `W⁻¹a ≤ ½(W⁻² + a²)` against the two summable series.
3. `ae_eq_torusScalarSeries` (new): the continuous series
   `torusScalarSeries v̂ᵢ` and `v` have the same `mFourierBasis.repr`
   (`fourier_repr_toLp` + `torusScalarSeries_coeff`), and `repr` is a
   `LinearIsometryEquiv`, so the two `Lp` elements are equal and the functions
   agree a.e.  Continuity of the series is `continuous_tsum` with `u = ‖c‖`.
4. `‖series x‖ ≤ ∑ₖ ‖c k‖` pointwise, then `ae_all_iff` over the three
   components and `PiLp.norm_sq_eq_of_L2` give
   `‖torusLift v y‖ ≤ Cinfty ‖A‖` a.e.; `essSup_le_of_ae_le` converts it to
   `eLpNorm … ⊤`.

Constant `Cinfty ≥ 1 > 0` because the `k = 0` term of `∑ W^{-2}` is `1`
(`Summable.le_tsum`).

## Dead ends / costs

* First attempt at step 3 tried to avoid `Lp`: bound `essSup` by a limit of
  `L^p` norms.  Abandoned — the Hilbert-basis route is three lines once
  `fourier_repr_toLp` is used on **both** functions.
* `positivity` cannot prove `0 ≤ periodicFrequencyWeight k ^ N` for a variable
  `N` (it does not know the base is positive), so
  `mul_nonneg (pow_nonneg (fourierWeight_pos k).le N) (norm_nonneg _)` is
  written out in `summable_lambdaCoeff_weighted`.
  Error text: `error: failed to prove positivity/nonnegativity/nonzeroness`.
* `rw [periodicSobolevENorm_eq hA]` leaves
  `ENNReal.ofReal c * ‖↑A‖ₑ = ENNReal.ofReal c * ‖A‖ₑ` (submodule norm vs.
  ambient norm): closed by a trailing `rfl`, not by `rw` alone.
* `if_pos` / `if_neg` are deprecated at `v4.34.0-rc2` (`logs/LESSONS.md`
  2026-09-18); the probe uses `simp only […, ↓reduceIte]` with an explicit
  `¬P` hypothesis instead.
* `MemPeriodicHmVector 2 v` carries `periodicSobolevENorm ((2 : ℕ) : ℝ) v ≠ ⊤`
  while the conclusion is at `(2 : ℝ)`; bridged by `simp only [Nat.cast_ofNat]`.

## Residual

None for the three targets.  The other six fields of the API
(`tameProduct`, `velocityCriticalL3`, `gradientLambdaCriticalL3`,
`gradientLSix`, `spectralGap`, `homogeneous_le_sobolev`) are out of this lane's
scope; `spectralGap` / `homogeneous_le_sobolev` are already in
`Section3/T12/SpectralGap.lean`.
