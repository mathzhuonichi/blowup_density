# B02 unit 7 (`low_high_split`) — attempts and notes

Target: field `lowHighSplit` of `research/B02/Spec.lean`'s `HomogeneousApproxAPI`
(`Spec.lean:421-425`), display `eq:Rnegative-cutoff`
(`04-whole-space.tex:242-248`). Proved in
`formalization/NSFormalization/Section4/B02/LowHigh.lean:199`
(`NSFormalization.Section4.B02.lowHighSplit`); conformance in
`research/B02/axioms_u7.lean`.

## Headline finding: the angular Plancherel was NOT in the tree

The task and COMPARISON row 7 both assumed an angular-convention Plancherel/isometry
existed ("`Source/FourierConvention.lean` should have `angularFourier`
Plancherel/isometry; grep `plancherel`, `norm_angularFourier`,
`eLpNorm_angularFourier`"). It does **not**. A thorough search (Mathlib +
`formalization` + `vendor`) found only:

* Schwartz-only pointwise Plancherel `SchwartzMap.integral_norm_sq_fourier`
  (Mathlib) and its angular corollary `angularSobolevSq_zero_eq_physical`
  (`Paper1/PeriodicScalarForceEndpoints.lean:30`) — both need `φ` Schwartz, not
  `L¹ ∩ L²`.
* The abstract `L²` isometry `MeasureTheory.Lp.norm_fourier_eq`
  (`Mathlib/Analysis/Fourier/LpSpace.lean:89`), stated on the *quotient* `Lp`, with
  **no** lemma tying its representative to the pointwise `fourierIntegral` beyond
  Schwartz.

`eq:Rnegative-cutoff`'s high half `∫_{|ξ|≥1}|k̂|² ≤ ‖k‖₂²` needs Plancherel at
`L¹ ∩ L²` (the manuscript applies the split to `(1−χ_R)h_n`, Schwartz but not
compactly supported; the spec correctly hypothesises `L¹ ∩ L²`, not compact
support). So the bridge had to be built. It is `angular_plancherel`
(`LowHigh.lean:185`), assembled from:

1. `fourier_mul_formula` (`:56`) — self-adjointness `∫ 𝓕φ·g = ∫ φ·𝓕g` via
   `VectorFourier.integral_fourierIntegral_smul_eq_flip`, the `ℝ³` inner form
   being symmetric (`(innerₗ Space).flip = innerₗ Space` by `real_inner_comm`).
2. `l2_fourier_pairing` (`:71`) / `coeFn_l2Fourier_ae` (`:86`) — the coefficient
   bridge: `(𝓕_{L²}(k.toLp) : Space → ℂ) =ᵐ 𝓕 k` for `k ∈ L¹ ∩ L²`, from
   `Lp.fourier_toTemperedDistribution_eq` (the `L²`-FT equals the `𝓢'`-FT) plus
   faithfulness `ae_eq_of_integral_contDiff_smul_eq`
   (`Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean:195`). The
   `𝓢'`-pairing is evaluated on real `C_c^∞` test functions, complexified through
   `NavierStokesR3.CompactSchwartz.ofCompactSupport`.
3. `eLpNorm_fourierIntegral_eq` (`:121`) — cycles Plancherel at `eLpNorm` level,
   from the bridge and `Lp.norm_fourier_eq` (+ `Lp.norm_def`, finiteness).
4. `angular_lintegral_eq_cycles` (`:153`) — the amplitude `(2π)^{-3/2}` squared
   `= (2π)^{-3}` exactly cancels the dilation Jacobian `(2π)^3`
   (`Measure.map_addHaar_smul` via `lintegral_comp_const_smul`, `:145`).

This bridge is exactly unit 6's (`homogeneous_datum_of_lebesgue`) core Plancherel
(shared with I03 `U7c`); COMPARISON calls unit 6 "the single blocker … built once
in a new Paper3 module". Unit 6 is not yet in the tree, so unit 7 had to build it
self-contained. If unit 6 lands, `angular_plancherel` / `coeFn_l2Fourier_ae`
should be promoted to a shared `Paper3` module and both lanes consume it.

## The main estimate

`HT:14 homogeneous_energy_le_bound_add_L2` was **not reused directly**: it is a
Bochner-`∫` statement and its high term `∫‖φ‖²` requires `Integrable ‖k̂‖²`, which
itself needs the Plancherel above. Instead its two-line majorant argument was
re-run entirely in `ℝ≥0∞` (no integrability side conditions), at angular radius 1:

* combine `∑_i ∫⁻ ofReal(|ξ|^{2s}·|k̂_i|²)` into `∫⁻ ofReal(|ξ|^{2s}·N)`,
  `N ξ = ∑_i|k̂_i(ξ)|²` (`lintegral_finsetSum'` + `ofReal_sum_of_nonneg`);
* split at `Metric.ball 0 1` (`lintegral_add_compl`);
* LOW: `N ξ ≤ C₀²` with `C₀ = (2π)^{-3/2}∫‖k‖` from unit 4's **vector**
  `fourierSupBound` (the vector form is load-bearing: a componentwise sup bound
  would cost a spurious factor 3 and break the constant), `lowFrequencyIntegrable`
  (unit 3) for the weight, `ofReal_integral_eq_lintegral_ofReal`, and
  `((2π)^{-3/2})² = (2π)^{-3}` gives `lowHighConstant s · ‖k‖₁²`;
* HIGH: `|ξ|^{2s} ≤ 1` on `‖ξ‖≥1` (`Real.rpow_le_one_of_one_le_of_nonpos`, `s≤0`),
  then `angular_plancherel` per component + `EuclideanSpace.norm_sq_eq` gives
  `‖k‖₂²`.

## Failed / abandoned approaches

* **Reusing `HT:14` in `ℝ`.** Rejected: needs `Integrable ‖angularFourier k_i‖²`,
  i.e. the Plancherel, before it can even be stated on `L¹ ∩ L²`. Circular unless
  the bridge is built first; re-running the majorant in `ℝ≥0∞` sidesteps it.
* **`Continuous.fourierIntegral` with `L := innerSL ℝ`.** `isDefEq` timeout
  (200000 heartbeats) against the `𝓕` notation, whose bilinear form is `innerₗ V`,
  not `innerSL`. Fixed by using `innerₗ Space` + `continuous_inner`.
* **`Continuous.rpow_const` / `fun_prop` for `‖ξ‖^{2s}`.** Not continuous at `0`
  for `s<0`; `fun_prop`/`Continuous.rpow_const` fail. `measurability` proves
  `Measurable (fun r:ℝ => r^{2s})`, composed with `measurable_norm`.
* **`Continuous.pow`/`.norm.pow` for the integrand.** Produces the Pi-power
  `(fun x=>‖·‖)^2`, which does not match the beta-reduced `‖·‖^2` in the goal for
  `lintegral_finsetSum'`. Fixed with `Measurable.pow_const 2` (gives `fun x=>f x^2`).
* **`ofReal_norm'`** (multiplicative `to_additive` source) resolves to
  `SeminormedGroup`; the additive `ofReal_norm` is the one that unifies with
  `NormedAddCommGroup`.
* Minor name/direction fixes: `ENNReal.toReal_eq_toReal_iff'` (not
  `toReal_eq_toReal`), `lintegral_finsetSum'` (not the deprecated
  `lintegral_finset_sum'`), `lintegral_const_mul'` (`r ≠ ∞`, no measurability
  side goal), `← ENNReal.ofReal_rpow_of_nonneg` direction.

## No `maxHeartbeats`, no `sorry`, no extra axioms

`#print axioms lowHighSplit = [propext, Classical.choice, Quot.sound]`. No
`maxHeartbeats … in` was needed anywhere.

## Commands

* `cd verification && lake build NSFormalization.Section4.B02.LowHigh`
  → `Build completed successfully (8780 jobs).`
* `cd verification && lake env lean ../research/B02/axioms_u7.lean`
  → `'NSFormalization.Section4.B02.lowHighSplit' depends on axioms:
     [propext, Classical.choice, Quot.sound]` (the spec-typed `example` closes).


## Review fixes (lead, 2026-09-13)

- Reviewer (`REVIEW_U7.md`) confirmed the Plancherel constant is exactly 1 and that no `L¹ ∩ L²` angular Plancherel existed in tree. Placement note: `LowHigh.lean:56-190` (`fourier_mul_formula`, `coeFn_l2Fourier_ae`, `eLpNorm_fourierIntegral_eq`, `angular_lintegral_eq_cycles`, `angular_plancherel`) is convention-level infrastructure to be promoted verbatim to a `Paper3` module by a follow-up MAINT lane so unit 6 and I03 U7c import it without depending on B02.
- Snag record: `fun_prop` fails only on the continuity goal (`0 ≤ 2 * s` unprovable); on the measurability goal it succeeds.
