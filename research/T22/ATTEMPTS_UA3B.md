# T22 U-A3b — closing the verbatim `cutoffMultiplier` field: attempts, positives and corrections

Lane 406 (Opus 5). Target: `BoundedDomainNormAPI.cutoffMultiplier`
(`formalization/NSFormalization/Section3/T22/Domain.lean`, `research/T22/Spec.lean:140-144`)
**verbatim**, on top of lane 397's engine `eLpNorm_cutoff_multiplier_le`
(`Section3/T22/CutoffMultiplier.lean`). Residuals R1–R4 as stated in
`research/T22/ATTEMPTS_UA3.md` §"Why the verbatim field is NOT closed".

## Result

**All four residuals closed.** New module
`formalization/NSFormalization/Section3/T22/CutoffMultiplierField.lean`; the final theorem is

```lean
theorem cutoffMultiplier : ∀ (s : ℝ) (χ : Space → ℝ),
    ContDiff ℝ ∞ χ → HasCompactSupport χ →
    ∃ C : ℝ, 0 < C ∧ ∀ A : RealVectorSobolev s,
      ∃ B : RealVectorSobolev s,
        IsCutoffDatum s χ A B ∧ ‖B‖ₑ ≤ ENNReal.ofReal C * ‖A‖ₑ
```

which is the field type on the nose (probe (a) in
`research/T22/probes/cutoff_multiplier_field_closes.lean` matches it by `exact` in both
directions). Every declaration prints `[propext, Classical.choice, Quot.sound]`.

The codex review of lane 397 (`research/T22/REVIEW_397-T22-UA3-cutoff-multiplier.md`, merged into this
branch) rejected 397 solely because the field was absent; its criterion probe
`research/T22/probes/rev397_field_target.lean` is reproduced verbatim — with the one extra import — in
`research/T22/probes/rev397_field_target_406.lean` and now closes by `exact`. The original probe is left
untouched as the record of that review.

## R1 — product ↔ convolution (the "long pole"): closed at the **Schwartz** level only

`ATTEMPTS_UA3.md` asked for the identity **at the `L²`/tempered level**, for a general datum
`A : RealVectorSobolev s`. That turned out to be the wrong target: it is not needed and was not proved.

What is proved instead:

1. `fourier_mul_eq_scalarConvolution (u v : 𝓢(Space,ℂ)) (ξ) :`
   `𝓕 (fun x => u x * v x) ξ = scalarConvolution (𝓕 ⇑u) (𝓕 ⇑v) ξ`.
   Mathlib's forward theorem is `SchwartzMap.fourier_convolution`
   (`𝓕 (convolution B f g) = pairing B (𝓕f) (𝓕g)`) together with the definitional
   `SchwartzMap.convolution B f g = 𝓕⁻ (pairing B (𝓕f) (𝓕g))`. Applying it to `f = 𝓕⁻u`, `g = 𝓕⁻v`
   and using `FourierTransform.fourier_fourierInv_eq` gives
   `SchwartzMap.convolution (mul ℂ ℂ) (𝓕⁻u) (𝓕⁻v) = 𝓕⁻ (u·v)`; `SchwartzMap.convolution_apply`
   turns the left side into the honest integral, and `Real.fourierInv_eq_fourier_neg` plus
   `MeasureTheory.integral_neg_eq_self` turn `𝓕⁻` into `𝓕`. No new analysis.
2. `angularFourier_mul (u v) (ξ) :`
   `angularFourier (fun x => u x * v x) ξ = frequencyUnit ^ (-3/2 : ℝ) • scalarConvolution (angularFourier ⇑u) (angularFourier ⇑v) ξ`
   — the normalization bookkeeping (`Measure.integral_comp_inv_smul_of_nonneg`, `finrank ℝ Space = 3`).

3. The lift to all `L²` data is **not** an identity but a *dense extension*: `LinearMap.extendOfNorm`
   (Mathlib `Analysis/Normed/Operator/Extend.lean`, the pattern already used in
   `Paper3/CompleteTameProduct.lean`) applied along `angularDatumL s : 𝓢(Space,ℂ) →L[ℝ] Lp ℂ 2 volume`,
   whose range is dense (`denseRange_angularCoordinateDatum` + the surjective isometry
   `angularFrequencyDilation`). This yields `cutoffOperator χ s : Lp ℂ 2 volume →L[ℝ] Lp ℂ 2 volume`
   with `cutoffOperator χ s (angularDatum s φ) = angularDatum s (χ·φ)` and
   `‖cutoffOperator χ s l‖ ≤ cutoffFieldConst s χ * ‖l‖`.

4. The **graph conjunct needs no convolution at all**: on the Schwartz core,
   `angularRealization s (angularDatum s φ) = (φ : 𝓢')` (`angularRealization_datum`) and
   `TemperedDistribution.smulLeftCLM ℂ χ_ℂ (φ : 𝓢') = ((χ·φ : 𝓢) : 𝓢')`
   (`smulLeftCLM_schwartz`, one `ext` + `integral_congr_ae`); both sides of
   `angularRealization_cutoffOperator` are continuous, so density closes it for every `l`.
   The convolution is needed **only** for the norm conjunct, via the a.e. identification
   `angularDatum_ae : ⇑(angularDatum s φ) =ᵐ fun ξ => besselW s ξ • angularFourier ⇑φ ξ`.

### Correction to `ATTEMPTS_UA3.md`'s R1 statement

The R1 formula there,
`b i := besselW s • scalarConvolution (angularFourier χ_ℂ) (besselW (-s) • (A i))`,
is **off by the angular amplitude**: in the manuscript's convention
`angularFourier f ξ = c^{-3/2} 𝓕f (c⁻¹ξ)` with `c = frequencyUnit = 2π`, the substitution `y = c z`
contributes a `c³` Jacobian that cancels only two of the three amplitudes, so the correct identity is
`angularFourier (u·v) = c^{-3/2} • (angularFourier u ∗ angularFourier v)`.
Written without that factor, R1 is false unless `frequencyUnit = 1`. Lane 406 absorbs it into the
constant instead of into `b`.

## R2 — real-subspace preservation: closed

`realSymmetry_angularDatum (s φ) : realSymmetry (angularDatum s φ) = angularDatum s (conjugateSchwartz φ)`
(three existing lemmas chained: `weightedFourierLp_conjugate`, `angularWeightEquiv_realSymmetry`,
`angularFrequencyDilation_realSymmetry`). Since `χ` is real-valued,
`conjugateSchwartz (χ·φ) = χ·(conjugateSchwartz φ)`, so on the dense core
`realSymmetry ∘ cutoffOperator = cutoffOperator ∘ realSymmetry`; both sides are continuous, hence
`realSymmetry_cutoffOperator` for all `l`, hence `cutoffOperator_mem_realSubspace`.

Note: the route did **not** use "real-evenness of `angularFourier χ_ℂ`" (`angularFourier_conj`) as
`ATTEMPTS_UA3.md` suggested; the reality argument is purely at the Schwartz/datum level, using the
reality pattern of `Section3/T22/OrderZero.lean` (lane 393) only as a model, not as an import.

## R3 — datum norm and vector assembly: closed, and `ATTEMPTS_UA3`/`REPORT_397` overstated the gap

No "datum-norm ↔ `eLpNorm`" lemma was needed: the datum **is** an `Lp ℂ 2 volume` element and
`RealSobolevHilbert s` is a subtype of it, so `‖A i‖` is already the `Lp` norm and `Lp.norm_def`
relates it to `eLpNorm` where the engine needs it.

The `PiLp 2` assembly is **in Mathlib**: `PiLp.norm_eq_of_L2 (x : PiLp 2 β) : ‖x‖ = √(∑ i, ‖x i‖ ^ 2)`
(`Mathlib/Analysis/Normed/Lp/PiLp.lean:779`; siblings `PiLp.norm_sq_eq_of_L2:791`,
`PiLp.nnnorm_eq_of_L2:785`, and `EuclideanSpace.norm_eq`). Lane 406 uses exactly
`PiLp.norm_eq_of_L2` twice plus `Real.sqrt_le_sqrt` / `Real.sqrt_mul` / `Real.sqrt_sq`, then
`ofReal_norm` and `ENNReal.ofReal_mul` to reach `‖B‖ₑ ≤ ofReal C * ‖A‖ₑ`. The claim in
`REPORT_397.md` that none of R1–R4 "has an in-tree proof" is corrected there.

## R4 — uniform positive constant: closed

`cutoffFieldConst s χ := frequencyUnit ^ (-3/2 : ℝ) * cutoffMultiplierConst s χ + 1`, positive for
every `χ` (including `χ = 0`) by `cutoffMultiplierConst_nonneg` and `Real.rpow_nonneg`. The `+1` is
harmless because the bounded quantity is a norm (`≥ 0`).

## Failed / rejected approaches (negatives)

- **Proving the `L²`-level product↔convolution identity (`ATTEMPTS_UA3.md`'s R1 as stated).**
  Not attempted to completion: once the dense-extension route was seen to give the graph for free
  (positive #4 above), the `L²` identity became unnecessary. It remains **unproved** in the tree,
  and the field does not depend on it. Anyone who needs `b i` in closed form for a general `L²`
  datum still owes it.
- **`rw [cutoffOperator_datum]` with `hχ`/`hc` left implicit.** After making `cutoffOperator` depend
  only on `χ` and `s` (so that `hχ`/`hc` are not unused binders in the `def`), `rw` on the
  dependent lemmas leaves an unsolved `case hχ` goal; the hypotheses must be passed explicitly
  (`rw [cutoffOperator_datum hχ hc]`). Same for `realSymmetry_cutoffOperator hχ hc`.
- **`nlinarith` for `a·n ≤ (a+1)·n`.** Fails when `set d := frequencyUnit ^ (-3/2)` has hidden the
  constant on one side only: `unfold cutoffFieldConst` re-introduces the unfolded spelling, and
  `linarith` cannot connect it to `d`. Fix: rewrite with the `set` equation (`← hdd`) first.
- **`rw [integral_neg_eq_self]` after `integral_congr_ae`.** The rewrite fails because the integrand
  is a beta-redex `(fun z => …) (-a)`; `exact integral_neg_eq_self (fun z => …) volume` works.
- **`angularRealization_datum` rewriting under `angularDatumL`.** `denseRange_angularDatumL`-driven
  induction presents the point as `angularDatumL s φ`, not `angularDatum s φ`; a
  `simp only [angularDatumL_apply]` is needed before the `rw` chain (a bare `change` only fixes the
  side you write out).
- **`SchwartzMap.injective_toLp` applied by `rw`.** Its statement is about
  `fun f => f.toLp p μ`, so the goal must be put in the form
  `psi.toLp 2 volume = (0 : 𝓢(Space,ℂ)).toLp 2 volume` with an explicit `show` first (probe file).

## Reuse index (what already existed and was used)

- Lane 397: `besselW`, `besselW_peetre`, `eLpNorm_cutoff_multiplier_le`, `cutoffMultiplierConst(_nonneg)`.
- Lane 391: `cutoffSchwartz`, `cutoffSchwartz_apply` (and, through 397, `integrable_weighted_fourier_cutoff`).
- `Paper3`: `angularDatum`, `angularRealization_datum`, `angularCoordinateDatum(_ae)`,
  `denseRange_angularCoordinateDatum`, `angularFrequencyDilation(_coeFn, _realSymmetry)`,
  `angularWeightEquiv_realSymmetry`.
- `Source.RealSobolev`: `realSymmetry`, `realSubspace`, `mem_realSubspace_iff`, `conjugateSchwartz`,
  `weightedFourierLp_conjugate`.
- Mathlib: `SchwartzMap.convolution`/`fourier_convolution`/`convolution_apply`,
  `Real.fourierInv_eq_fourier_neg`, `MeasureTheory.integral_neg_eq_self`,
  `Measure.integral_comp_inv_smul_of_nonneg`, `LinearMap.extendOfNorm(_eq)`,
  `LinearMap.norm_extendOfNorm_apply_le`, `PiLp.norm_eq_of_L2`, `ofReal_norm`,
  `SchwartzMap.injective_toLp`, `MeasureTheory.Lp.toTemperedDistribution_toLp_eq`,
  `Lp.ker_toTemperedDistributionCLM_eq_bot`.
