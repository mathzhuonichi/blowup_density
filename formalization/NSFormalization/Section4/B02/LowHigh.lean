import NSFormalization.Section4.B02.LowFrequency
import NavierStokes.R3.CompactSchwartz
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# B02, unit 7: the low/high-frequency split `eq:Rnegative-cutoff`

This module discharges the field `lowHighSplit` of `research/B02/Spec.lean`'s
`HomogeneousApproxAPI`, the display `eq:Rnegative-cutoff`
(`paper/sections/04-whole-space.tex:242-248`): for every real vector field
`k ∈ L¹ ∩ L²` and every order `s` with `-3/2 < s ≤ 0`,

  `‖k‖²_{Ḣ^s} ≤ C_s ‖k‖₁² + ‖k‖₂²`,   `C_s = (2π)^{-3} ∫_{|ξ|<1} |ξ|^{2s} dξ`,

stated in `ℝ≥0∞` with `Ḣ^s` energy `homogeneousFourierENorm`, in the manuscript's
unitary angular Fourier convention (`Source.angularFourier`).

## Proof outline

The estimate is `HT:14`'s scalar majorant argument re-run at *angular* radius `1`
and summed over the three components, feeding unit 4's vector `L¹→L∞` bound
(`fourierSupBound`) for the low half, `Real.rpow_le_one_of_one_le_of_nonpos` for
the high half, and unit 3's `lowFrequencyIntegrable` for the finiteness of the
low-frequency weight.  The high half also needs Plancherel in the angular
convention, `∫ |k̂|² = ‖k‖₂²`, which is *not* present in the tree at the
`L¹ ∩ L²` level (only the Schwartz `SchwartzMap.integral_norm_sq_fourier` and the
abstract `Lp.norm_fourier_eq`).  It is built here, over `angular_plancherel`:

* `fourier_mul_formula`: the self-adjointness `∫ 𝓕φ • g = ∫ φ • 𝓕g`
  (`VectorFourier.integral_fourierIntegral_smul_eq_flip`, the inner form being
  symmetric).
* `l2_fourier_pairing` / `coeFn_l2Fourier_ae`: the coefficient bridge.  The
  abstract `L²` Fourier transform's representative agrees a.e. with the pointwise
  `fourierIntegral` on `L¹ ∩ L²`, via
  `MeasureTheory.Lp.fourier_toTemperedDistribution_eq` and the faithfulness
  `ae_eq_of_integral_contDiff_smul_eq`.
* `eLpNorm_fourierIntegral_eq`: cycles Plancherel at the `eLpNorm` level, from the
  bridge and `Lp.norm_fourier_eq`.
* `angular_lintegral_eq_cycles`: the amplitude `(2π)^{-3/2}` exactly cancels the
  dilation volume `(2π)^3` (`Measure.map_addHaar_smul`), so the angular and cycles
  energies coincide.

Everything is in `ℝ≥0∞`, so no field has to be assumed finite.
-/

open MeasureTheory Set NavierStokes.ProblemStatement NSFormalization.Source
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ContDiff

noncomputable section

namespace NSFormalization.Section4.B02

/-- Self-adjointness of the (cycles) Fourier transform, `∫ 𝓕φ • g = ∫ φ • 𝓕g`,
on integrable `φ, g`.  The `ℝ³` inner form is symmetric, so `L.flip = L`. -/
theorem fourier_mul_formula (g φ : Space → ℂ)
    (hφ : Integrable φ volume) (hg : Integrable g volume) :
    ∫ ξ, (𝓕 φ ξ) • g ξ = ∫ x, (φ x) • (𝓕 g x) := by
  have hflip : (innerₗ Space).flip = innerₗ Space := by
    ext x y
    simp only [LinearMap.flip_apply, innerₗ_apply_apply]
    exact real_inner_comm x y
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (μ := (volume : Measure Space)) (ν := (volume : Measure Space))
    (L := innerₗ Space) (f := φ) (g := g) Real.continuous_fourierChar continuous_inner hφ hg
  rw [hflip] at h
  exact h

/-- The distribution of the abstract `L²` Fourier transform of `k ∈ L² ` pairs
against a Schwartz test function `φ` as `∫ φ • 𝓕k`, using the `𝓢'` identity
`Lp.fourier_toTemperedDistribution_eq` and `fourier_mul_formula`. -/
theorem l2_fourier_pairing (g : Space → ℂ) (hg1 : Integrable g volume)
    (hg2 : MemLp g 2 volume) (φ : SchwartzMap Space ℂ) :
    (((𝓕 (hg2.toLp g) : Lp ℂ 2 (volume : Measure Space))) : 𝓢'(Space, ℂ)) φ
      = ∫ ξ, (φ ξ) • 𝓕 g ξ := by
  rw [← Lp.fourier_toTemperedDistribution_eq (hg2.toLp g)]
  rw [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply]
  have hcoe : (fun x => ((𝓕 φ : SchwartzMap Space ℂ) x) • (hg2.toLp g) x)
      =ᵐ[volume] (fun x => (𝓕 (⇑φ) x) • g x) := by
    filter_upwards [hg2.coeFn_toLp] with x hx
    rw [hx, SchwartzMap.fourier_coe]
  rw [integral_congr_ae hcoe, fourier_mul_formula g (φ : Space → ℂ) (φ.integrable) hg1]

/-- The coefficient bridge: for `g ∈ L¹ ∩ L²`, the representative of the abstract
`L²` Fourier transform agrees a.e. with the pointwise cycles integral `𝓕 g`. -/
theorem coeFn_l2Fourier_ae (g : Space → ℂ) (hg1 : Integrable g volume)
    (hg2 : MemLp g 2 volume) :
    (fun ξ => ((𝓕 (hg2.toLp g) : Lp ℂ 2 (volume : Measure Space)) : Space → ℂ) ξ)
      =ᵐ[volume] (fun ξ => 𝓕 g ξ) := by
  set u : Space → ℂ := ((𝓕 (hg2.toLp g) : Lp ℂ 2 (volume : Measure Space)) : Space → ℂ) with hu
  set v : Space → ℂ := fun ξ => 𝓕 g ξ with hv
  have hu_li : LocallyIntegrable u volume :=
    (Lp.memLp (𝓕 (hg2.toLp g))).locallyIntegrable (by norm_num)
  have hv_li : LocallyIntegrable v volume :=
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (L := innerₗ Space) continuous_inner hg1).locallyIntegrable
  apply ae_eq_of_integral_contDiff_smul_eq hu_li hv_li
  intro φ hφcd hφcs
  have hcd : ContDiff ℝ ∞ (fun x => (φ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hφcd
  have hcs : HasCompactSupport (fun x => (φ x : ℂ)) :=
    hφcs.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  set Φ : SchwartzMap Space ℂ := NavierStokesR3.CompactSchwartz.ofCompactSupport
    (fun x => (φ x : ℂ)) hcd hcs with hΦ
  have hΦval : ∀ x, (Φ x) = (φ x : ℂ) := fun _ => rfl
  have hpair : (∫ x, (Φ x) • u x) = ∫ ξ, (Φ ξ) • v ξ := by
    have h1 : (((𝓕 (hg2.toLp g) : Lp ℂ 2 (volume : Measure Space))) : 𝓢'(Space, ℂ)) Φ
        = ∫ x, (Φ x) • u x := Lp.toTemperedDistribution_apply _ Φ
    have h2 := l2_fourier_pairing g hg1 hg2 Φ
    rw [h1] at h2; exact h2
  calc ∫ x, φ x • u x
      = ∫ x, (Φ x) • u x := by
        apply integral_congr_ae; filter_upwards [] with x
        simp only [hΦval, Complex.real_smul, smul_eq_mul]
    _ = ∫ ξ, (Φ ξ) • v ξ := hpair
    _ = ∫ ξ, φ ξ • v ξ := by
        apply integral_congr_ae; filter_upwards [] with x
        simp only [hΦval, Complex.real_smul, smul_eq_mul]

/-- Cycles Plancherel at the `eLpNorm` level: `‖𝓕 g‖₂ = ‖g‖₂` for `g ∈ L¹ ∩ L²`,
transferred from the abstract `Lp.norm_fourier_eq` along the coefficient bridge. -/
theorem eLpNorm_fourierIntegral_eq (g : Space → ℂ) (hg1 : Integrable g volume)
    (hg2 : MemLp g 2 volume) :
    eLpNorm (fun ξ => 𝓕 g ξ) 2 volume = eLpNorm g 2 volume := by
  rw [← eLpNorm_congr_ae (coeFn_l2Fourier_ae g hg1 hg2)]
  have h1 : eLpNorm (((𝓕 (hg2.toLp g) : Lp ℂ 2 (volume : Measure Space)) : Space → ℂ)) 2 volume
      = eLpNorm ((hg2.toLp g : Lp ℂ 2 (volume : Measure Space)) : Space → ℂ) 2 volume := by
    have hnorm := Lp.norm_fourier_eq (hg2.toLp g)
    rw [Lp.norm_def, Lp.norm_def] at hnorm
    exact (ENNReal.toReal_eq_toReal_iff' (Lp.eLpNorm_lt_top _).ne (Lp.eLpNorm_lt_top _).ne).mp hnorm
  rw [h1]
  exact eLpNorm_congr_ae hg2.coeFn_toLp

/-- `‖f‖₂² = ∫⁻ ‖f x‖ₑ² dx`, for any codomain. -/
theorem sq_eLpNorm_two {E : Type*} [NormedAddCommGroup E] (f : Space → E) :
    eLpNorm f 2 volume ^ (2:ℝ) = ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂(volume : Measure Space) := by
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num)]
  unfold eLpNorm'
  rw [← ENNReal.rpow_mul]
  norm_num

theorem finrank_space_eq_three : Module.finrank ℝ Space = 3 := by
  simp [Space, finrank_euclideanSpace]

/-- Change of variables for a homothety on `ℝ³` in the lower Lebesgue integral. -/
theorem lintegral_comp_const_smul (F : Space → ℝ≥0∞) (hF : Measurable F) {a : ℝ} (ha : a ≠ 0) :
    (∫⁻ ξ, F (a • ξ) ∂(volume : Measure Space))
      = ENNReal.ofReal (|(a ^ 3)⁻¹|) * ∫⁻ η, F η ∂(volume : Measure Space) := by
  rw [← lintegral_map hF (continuous_const_smul a).measurable,
    Measure.map_addHaar_smul volume ha, finrank_space_eq_three, lintegral_smul_measure, smul_eq_mul]

/-- The angular and cycles homogeneous `L²` energies coincide: the amplitude
`(2π)^{-3/2}` squared cancels the `(2π)^3` dilation Jacobian. -/
theorem angular_lintegral_eq_cycles (g : Space → ℂ) (hg1 : Integrable g volume) :
    (∫⁻ ξ, ‖angularFourier g ξ‖ₑ ^ (2:ℝ) ∂(volume : Measure Space))
      = ∫⁻ η, ‖𝓕 g η‖ₑ ^ (2:ℝ) ∂(volume : Measure Space) := by
  have hcF : Continuous (fun η : Space => 𝓕 g η) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (L := innerₗ Space) continuous_inner hg1
  have hFmeas : Measurable (fun η : Space => ‖𝓕 g η‖ₑ ^ (2:ℝ)) :=
    (hcF.enorm.measurable).pow_const _
  have hpt : ∀ ξ, ‖angularFourier g ξ‖ₑ ^ (2:ℝ)
      = ‖(frequencyUnit ^ (-3/2 : ℝ) : ℝ)‖ₑ ^ (2:ℝ) * ‖𝓕 g (frequencyUnit⁻¹ • ξ)‖ₑ ^ (2:ℝ) := by
    intro ξ
    unfold angularFourier
    rw [enorm_smul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  have hginn : Measurable (fun ξ : Space => ‖𝓕 g (frequencyUnit⁻¹ • ξ)‖ₑ ^ (2:ℝ)) :=
    ((hcF.comp (continuous_const_smul (frequencyUnit⁻¹))).enorm.measurable).pow_const _
  simp_rw [hpt]
  rw [lintegral_const_mul _ hginn,
    lintegral_comp_const_smul (fun η => ‖𝓕 g η‖ₑ ^ (2:ℝ)) hFmeas (by simp [frequencyUnit_pos.ne']),
    ← mul_assoc]
  have ht : (0:ℝ) < frequencyUnit := frequencyUnit_pos
  have hprod : (frequencyUnit ^ (-3/2:ℝ)) ^ (2:ℝ) * |((frequencyUnit⁻¹) ^ 3)⁻¹| = 1 := by
    rw [inv_pow, inv_inv, abs_of_nonneg (by positivity), ← Real.rpow_natCast frequencyUnit 3,
      ← Real.rpow_mul ht.le, ← Real.rpow_add ht,
      show (-3/2:ℝ) * 2 + ((3:ℕ):ℝ) = 0 by push_cast; ring, Real.rpow_zero]
  have hb1 : ‖(frequencyUnit ^ (-3/2 : ℝ) : ℝ)‖ₑ ^ (2:ℝ)
      = ENNReal.ofReal ((frequencyUnit ^ (-3/2:ℝ)) ^ (2:ℝ)) := by
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (Real.rpow_nonneg ht.le _),
      ← ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg ht.le _) (by norm_num)]
  rw [hb1, ← ENNReal.ofReal_mul (by positivity), hprod, ENNReal.ofReal_one, one_mul]

/-- Plancherel in the angular convention on `L¹ ∩ L²`:
`∫ |angularFourier g|² = ‖g‖₂²`. -/
theorem angular_plancherel (g : Space → ℂ) (hg1 : Integrable g volume)
    (hg2 : MemLp g 2 volume) :
    (∫⁻ ξ, ‖angularFourier g ξ‖ₑ ^ (2:ℝ) ∂(volume : Measure Space))
      = ∫⁻ x, ‖g x‖ₑ ^ (2:ℝ) ∂(volume : Measure Space) := by
  rw [angular_lintegral_eq_cycles g hg1, ← sq_eLpNorm_two, ← sq_eLpNorm_two,
    eLpNorm_fourierIntegral_eq g hg1 hg2]

/-- `research/B02/Spec.lean:421` `lowHighSplit`, `04-whole-space.tex:242-248`
`eq:Rnegative-cutoff`: for `k ∈ L¹ ∩ L²` and `-3/2 < s ≤ 0`, the homogeneous
`Ḣ^s` energy splits at angular radius `1` into a low part controlled by
`(2π)^{-3} ∫_{|ξ|<1}|ξ|^{2s} · ‖k‖₁²` and a high part controlled by `‖k‖₂²`.
Stated in `ℝ≥0∞`; the left side is the definitional body of
`Data.lean`'s `homogeneousFourierENorm s k ^ (2:ℝ)` and the constant is
`Spec.lean`'s `lowHighConstant s`. -/
theorem lowHighSplit (s : ℝ) (hs : -3/2 < s) (hs0 : s ≤ 0)
    (k : Space → Space) (hk1 : MemLp k 1 volume) (hk2 : MemLp k 2 volume) :
    ((∑ i : Fin 3, ∫⁻ ξ : Space,
        ENNReal.ofReal (‖ξ‖ ^ (2 * s) *
          ‖angularFourier (fun x => ((k x i : ℝ) : ℂ)) ξ‖ ^ 2)) ^ ((2:ℝ)⁻¹)) ^ (2:ℝ) ≤
      ENNReal.ofReal ((2 * Real.pi) ^ (-(3:ℝ)) * ∫ ξ in Metric.ball (0:Space) 1, ‖ξ‖ ^ (2*s))
        * eLpNorm k 1 volume ^ (2:ℝ) + eLpNorm k 2 volume ^ (2:ℝ) := by
  set g : Fin 3 → Space → ℂ := fun i x => ((k x i : ℝ) : ℂ) with hgdef
  have hk1i : Integrable k volume := (memLp_one_iff_integrable).mp hk1
  have hg_aesm : ∀ i, AEStronglyMeasurable (g i) volume := fun i =>
    (Complex.continuous_ofReal.comp (EuclideanSpace.proj i).continuous).comp_aestronglyMeasurable
      hk2.aestronglyMeasurable
  have hg_le : ∀ i, ∀ x, ‖g i x‖ ≤ ‖k x‖ := by
    intro i x
    have hxeq : ‖g i x‖ = ‖k x i‖ := by simp [hgdef, Complex.norm_real]
    rw [hxeq]; exact PiLp.norm_apply_le (k x) i
  have hg1 : ∀ i, Integrable (g i) volume := fun i =>
    memLp_one_iff_integrable.mp (hk1.of_le (hg_aesm i) (ae_of_all _ (hg_le i)))
  have hg2 : ∀ i, MemLp (g i) 2 volume := fun i =>
    hk2.of_le (hg_aesm i) (ae_of_all _ (hg_le i))
  have hcont : ∀ i, Continuous (fun ξ => angularFourier (g i) ξ) := by
    intro i
    unfold angularFourier
    exact ((VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        (L := innerₗ Space) continuous_inner (hg1 i)).comp
          (continuous_const_smul (frequencyUnit⁻¹))).const_smul (frequencyUnit ^ (-3/2:ℝ))
  -- generic helper: ofReal (‖z‖²) = ‖z‖ₑ^(2:ℝ)
  have hnormsq : ∀ {E : Type} [inst : NormedAddCommGroup E] (z : E),
      ENNReal.ofReal (‖z‖ ^ 2) = ‖z‖ₑ ^ (2:ℝ) := by
    intro E inst z
    have he : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := (ofReal_norm z).symm
    rw [he, ENNReal.rpow_two, ← ENNReal.ofReal_pow (norm_nonneg z)]
  -- weight + integrand measurability
  have hw_meas : Measurable (fun ξ : Space => ‖ξ‖ ^ (2*s)) :=
    (by measurability : Measurable (fun r : ℝ => r ^ (2*s))).comp measurable_norm
  have hmn : ∀ i, Measurable (fun ξ : Space => ‖angularFourier (g i) ξ‖ ^ 2) := fun i =>
    (hcont i).norm.measurable.pow_const 2
  have hint_meas : ∀ i, Measurable (fun ξ : Space =>
      ENNReal.ofReal (‖ξ‖ ^ (2*s) * ‖angularFourier (g i) ξ‖ ^ 2)) := fun i =>
    (hw_meas.mul (hmn i)).ennreal_ofReal
  have hm : ∀ i, Measurable (fun ξ : Space =>
      ENNReal.ofReal (‖angularFourier (g i) ξ‖ ^ 2)) := fun i => (hmn i).ennreal_ofReal
  -- eLpNorm k 1 as an ofReal
  have heL1 : eLpNorm k 1 volume = ENNReal.ofReal (∫ x, ‖k x‖) := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hk1i]
  -- rewrite the goal to use angularFourier (g i)
  have hAF : ∀ i : Fin 3, (fun x => ((k x i : ℝ) : ℂ)) = g i := fun _ => rfl
  simp only [hAF]
  -- Step A: collapse the outer rpow
  rw [← ENNReal.rpow_mul, show (2:ℝ)⁻¹ * 2 = 1 by norm_num, ENNReal.rpow_one]
  -- combine sum into single integral of the vector energy
  set N : Space → ℝ := fun ξ => ∑ i : Fin 3, ‖angularFourier (g i) ξ‖ ^ 2 with hN
  have hNnonneg : ∀ ξ, 0 ≤ N ξ := fun ξ => Finset.sum_nonneg (fun i _ => by positivity)
  have hcomb : (∑ i : Fin 3, ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (2*s) * ‖angularFourier (g i) ξ‖ ^ 2))
      = ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (2*s) * N ξ) := by
    rw [← lintegral_finsetSum' Finset.univ (fun i _ => (hint_meas i).aemeasurable)]
    apply lintegral_congr; intro ξ
    rw [hN, Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  rw [hcomb, ← lintegral_add_compl (fun ξ => ENNReal.ofReal (‖ξ‖ ^ (2*s) * N ξ))
    measurableSet_ball]
  -- nonnegativity of the two scalar integrals
  have hballnn : 0 ≤ ∫ ξ in Metric.ball (0:Space) 1, ‖ξ‖ ^ (2*s) :=
    setIntegral_nonneg measurableSet_ball (fun ξ _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hkL1nn : 0 ≤ ∫ x, ‖k x‖ := integral_nonneg (fun x => norm_nonneg _)
  -- LOW half
  set C0 : ℝ := (2*Real.pi) ^ (-(3:ℝ)/2) * ∫ x, ‖k x‖ with hC0
  have hsup : ∀ ξ, N ξ ≤ C0 ^ 2 := by
    intro ξ
    have hfsb := NSFormalization.Section4.B02.fourierSupBound k hk1 ξ
    have hle : Real.sqrt (N ξ) ≤ C0 := by rw [hN, hC0]; exact hfsb
    calc N ξ = Real.sqrt (N ξ) ^ 2 := by rw [Real.sq_sqrt (hNnonneg ξ)]
      _ ≤ C0 ^ 2 := by nlinarith [hle, Real.sqrt_nonneg (N ξ)]
  have hlow : (∫⁻ ξ in Metric.ball (0:Space) 1, ENNReal.ofReal (‖ξ‖ ^ (2*s) * N ξ))
      ≤ ENNReal.ofReal ((2*Real.pi)^(-(3:ℝ)) * ∫ ξ in Metric.ball (0:Space) 1, ‖ξ‖ ^ (2*s))
        * eLpNorm k 1 volume ^ (2:ℝ) := by
    have hstep1 : (∫⁻ ξ in Metric.ball (0:Space) 1, ENNReal.ofReal (‖ξ‖ ^ (2*s) * N ξ))
        ≤ ∫⁻ ξ in Metric.ball (0:Space) 1,
            ENNReal.ofReal (C0^2) * ENNReal.ofReal (‖ξ‖ ^ (2*s)) := by
      apply lintegral_mono; intro ξ
      dsimp only
      rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ C0^2)]
      apply ENNReal.ofReal_le_ofReal
      nlinarith [hsup ξ, hNnonneg ξ, Real.rpow_nonneg (norm_nonneg ξ) (2*s)]
    refine le_trans hstep1 (le_of_eq ?_)
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← ofReal_integral_eq_lintegral_ofReal
        (NSFormalization.Section4.B02.lowFrequencyIntegrable s hs)
        (ae_of_all _ (fun ξ => Real.rpow_nonneg (norm_nonneg _) _)),
      ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ C0^2),
      heL1, ENNReal.rpow_two, ← ENNReal.ofReal_pow hkL1nn,
      ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (by positivity) _) hballnn)]
    congr 1
    have hpow : ((2*Real.pi)^(-(3:ℝ)/2))^(2:ℕ) = (2*Real.pi)^(-(3:ℝ)) := by
      rw [← Real.rpow_natCast ((2*Real.pi)^(-(3:ℝ)/2)) 2, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [hC0, mul_pow, hpow]
    ring
  -- HIGH half
  have hhigh : (∫⁻ ξ in (Metric.ball (0:Space) 1)ᶜ, ENNReal.ofReal (‖ξ‖ ^ (2*s) * N ξ))
      ≤ eLpNorm k 2 volume ^ (2:ℝ) := by
    have hstep1 : (∫⁻ ξ in (Metric.ball (0:Space) 1)ᶜ, ENNReal.ofReal (‖ξ‖ ^ (2*s) * N ξ))
        ≤ ∫⁻ ξ in (Metric.ball (0:Space) 1)ᶜ, ENNReal.ofReal (N ξ) := by
      apply setLIntegral_mono_ae' measurableSet_ball.compl
      filter_upwards [] with ξ hξ
      apply ENNReal.ofReal_le_ofReal
      have h1 : (1:ℝ) ≤ ‖ξ‖ := by
        simpa [mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hξ
      nlinarith [Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith : 2*s ≤ 0), hNnonneg ξ]
    have hstep3 : (∫⁻ ξ, ENNReal.ofReal (N ξ)) = eLpNorm k 2 volume ^ (2:ℝ) := by
      have he1 : (∫⁻ ξ, ENNReal.ofReal (N ξ))
          = ∑ i : Fin 3, ∫⁻ ξ, ENNReal.ofReal (‖angularFourier (g i) ξ‖ ^ 2) := by
        rw [← lintegral_finsetSum' Finset.univ (fun i _ => (hm i).aemeasurable)]
        apply lintegral_congr; intro ξ
        rw [hN, ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
      have he2 : ∀ i, (∫⁻ ξ, ENNReal.ofReal (‖angularFourier (g i) ξ‖ ^ 2))
          = ∫⁻ x, ENNReal.ofReal (‖g i x‖ ^ 2) := by
        intro i; simp_rw [hnormsq]; exact angular_plancherel (g i) (hg1 i) (hg2 i)
      rw [he1]; simp_rw [he2]
      rw [← lintegral_finsetSum' Finset.univ
        (fun i _ => (((hg_aesm i).norm.aemeasurable).pow_const 2).ennreal_ofReal)]
      have he3 : ∀ x, (∑ i : Fin 3, ENNReal.ofReal (‖g i x‖ ^ 2))
          = ENNReal.ofReal (‖k x‖ ^ 2) := by
        intro x
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity),
          EuclideanSpace.norm_sq_eq (k x)]
        congr 1
        exact Finset.sum_congr rfl (fun i _ => by rw [hgdef]; simp [Complex.norm_real])
      simp_rw [he3, hnormsq]
      exact (sq_eLpNorm_two k).symm
    exact le_trans hstep1 (le_trans (setLIntegral_le_lintegral _ _) (le_of_eq hstep3))
  exact add_le_add hlow hhigh

end NSFormalization.Section4.B02
