import NSFormalization.Section4.C01.EnstrophyIdentityRaw

/-!
# P21 Route B, B1: inhomogeneous differentiated energy on R³

The revised article, `paper/revised/sections/02-preliminaries.tex:149–156`, says:
“For each initial velocity in the stated class and each force smooth into
 every H^m on compact time intervals ... a unique maximal smooth velocity” and
“[if] ∫₀ˢ ‖u(t)‖²_H² dt < ∞, then it extends smoothly beyond S”.
This module develops the general energy estimate for the separate H¹-uniform
restart obligation, not a newly displayed clause of that proposition.

`C01.enstrophyIdentity_gradientSq` differentiates only ∫|∇u|². Adding
`C01.energyIdentity_l2Sq` retains the L² energy, gradient dissipation and
ordinary force work. Identification with the registered Fourier norm is a B0
bridge, not implicit in the physical identity below.
-/

noncomputable section
open Set MeasureTheory
open NSFormalization.Section4.C01
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A05 (lap gradTensor SmoothL2 dirDeriv gradientL6Const)
open scoped ENNReal
namespace NSFormalization.Section4.A04

/-- Exact inhomogeneous physical H¹ energy identity, without smallness. -/
theorem inhomogeneousEnergyIdentity
    {ν T : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField}
    (w : A02.ClassicalSolutionR ν a f T) (hf : A02.MemForceR f)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt
      (fun s => l2Sq (slice w.velocity s) + gradientSq (slice w.velocity s))
      (-2 * ν * (gradientSq (slice w.velocity t) + laplacianSq (slice w.velocity t)) +
        2 * advectionWork (slice w.velocity t) +
        2 * pairing (slice w.velocity t) (slice f t) -
        2 * pairing (slice f t) (A05.lap (slice w.velocity t))) t := by
  have h := (energyIdentity_l2Sq w hf ht).add (enstrophyIdentity_gradientSq w hf ht)
  convert h using 1 <;> first | rfl | (simp only [gradientSq]; ring)

/-- Three-factor Hölder with velocity in L⁶ and gradient in L³. -/
theorem lintegral_convection_holder_632 (z : Space → Space) (hz : SmoothL2 z) :
    ∫⁻ x, ‖(inner ℝ (advection (lift z) 0 x) (lap z x) : ℝ)‖ₑ ∂volume ≤
      eLpNorm z 6 volume * eLpNorm (gradTensor z) 3 volume * eLpNorm (lap z) 2 volume := by
  -- continuity, hence measurability, of the three fields
  have hcz : Continuous z := hz.contDiff.continuous
  have hcg : Continuous (gradTensor z) := by
    show Continuous (fun x =>
      (WithLp.toLp 2 (fun j : Fin 3 => dirDeriv j z x) : WithLp 2 (Fin 3 → Space)))
    exact Continuous.comp (PiLp.continuous_toLp 2 (fun _ : Fin 3 => Space))
      (continuous_pi fun j => (hz.dir j).contDiff.continuous)
  have hcl : Continuous (lap z) :=
    continuous_finsetSum _ (fun i _ => ((hz.dir i).dir i).contDiff.continuous)
  -- pointwise enorm bound on the integrand
  have hpt : ∀ x : Space,
      ‖(inner ℝ (advection (lift z) 0 x) (lap z x) : ℝ)‖ₑ ≤
        ‖z x‖ₑ * ‖gradTensor z x‖ₑ * ‖lap z x‖ₑ := by
    intro x
    have hcs : |(inner ℝ (advection (lift z) 0 x) (lap z x) : ℝ)| ≤
        ‖advection (lift z) 0 x‖ * ‖lap z x‖ := abs_real_inner_le_norm _ _
    have hreal : |(inner ℝ (advection (lift z) 0 x) (lap z x) : ℝ)| ≤
        ‖z x‖ * ‖gradTensor z x‖ * ‖lap z x‖ :=
      hcs.trans (mul_le_mul_of_nonneg_right (advection_norm_le z x) (norm_nonneg _))
    calc ‖(inner ℝ (advection (lift z) 0 x) (lap z x) : ℝ)‖ₑ
        = ENNReal.ofReal |(inner ℝ (advection (lift z) 0 x) (lap z x) : ℝ)| :=
          Real.enorm_eq_ofReal_abs _
      _ ≤ ENNReal.ofReal (‖z x‖ * ‖gradTensor z x‖ * ‖lap z x‖) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ‖z x‖ₑ * ‖gradTensor z x‖ₑ * ‖lap z x‖ₑ := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (norm_nonneg _),
            ofReal_norm, ofReal_norm, ofReal_norm]
  -- three-factor Hölder in `ℝ≥0∞`
  have hpow : ∀ (a : ℝ≥0∞) (k : ℝ), 0 < k → (a ^ k) ^ (1 / k) = a := by
    intro a k hk
    rw [← ENNReal.rpow_mul, mul_one_div, div_self (ne_of_gt hk), ENNReal.rpow_one]
  have hez : (∫⁻ x, ‖z x‖ₑ ^ (6 : ℝ) ∂volume) ^ ((1 : ℝ) / 6) = eLpNorm z 6 volume := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat]
  have heg : (∫⁻ x, ‖gradTensor z x‖ₑ ^ (3 : ℝ) ∂volume) ^ ((1 : ℝ) / 3)
      = eLpNorm (gradTensor z) 3 volume := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat]
  have hel : (∫⁻ x, ‖lap z x‖ₑ ^ (2 : ℝ) ∂volume) ^ ((1 : ℝ) / 2)
      = eLpNorm (lap z) 2 volume := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat]
  have hHolder : ∫⁻ x, ‖z x‖ₑ * ‖gradTensor z x‖ₑ * ‖lap z x‖ₑ ∂volume ≤
      eLpNorm z 6 volume * eLpNorm (gradTensor z) 3 volume * eLpNorm (lap z) 2 volume := by
    calc ∫⁻ x, ‖z x‖ₑ * ‖gradTensor z x‖ₑ * ‖lap z x‖ₑ ∂volume
        = ∫⁻ x, ∏ i : Fin 3,
            (![fun x => ‖z x‖ₑ ^ (6 : ℝ), fun x => ‖gradTensor z x‖ₑ ^ (3 : ℝ),
              fun x => ‖lap z x‖ₑ ^ (2 : ℝ)] i x) ^
              (![(1 : ℝ) / 6, 1 / 3, 1 / 2] i) ∂volume := by
          refine lintegral_congr (fun x => ?_)
          rw [Fin.prod_univ_three]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            Matrix.cons_val_two, Matrix.tail_cons]
          rw [hpow (‖z x‖ₑ) 6 (by norm_num), hpow (‖gradTensor z x‖ₑ) 3 (by norm_num),
            hpow (‖lap z x‖ₑ) 2 (by norm_num)]
      _ ≤ ∏ i : Fin 3,
            (∫⁻ x, (![fun x => ‖z x‖ₑ ^ (6 : ℝ), fun x => ‖gradTensor z x‖ₑ ^ (3 : ℝ),
              fun x => ‖lap z x‖ₑ ^ (2 : ℝ)] i x) ∂volume) ^ (![(1 : ℝ) / 6, 1 / 3, 1 / 2] i) := by
          refine ENNReal.lintegral_prod_norm_pow_le (Finset.univ) ?_ ?_ ?_
          · intro i _
            fin_cases i
            · exact ((continuous_enorm.comp hcz).aemeasurable).pow_const _
            · exact ((continuous_enorm.comp hcg).aemeasurable).pow_const _
            · exact ((continuous_enorm.comp hcl).aemeasurable).pow_const _
          · norm_num [Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
          · intro i _
            fin_cases i <;> norm_num
      _ = eLpNorm z 6 volume * eLpNorm (gradTensor z) 3 volume * eLpNorm (lap z) 2 volume := by
          rw [Fin.prod_univ_three]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            Matrix.cons_val_two, Matrix.tail_cons]
          rw [hez, heg, hel]
  exact (lintegral_mono hpt).trans hHolder


/-- L³ interpolation between L² and L⁶, including infinite norms. -/
theorem eLpNorm_three_interpolation {E : Type*} [NormedAddCommGroup E] (g : NavierStokes.ProblemStatement.Space → E)
    (hg : AEStronglyMeasurable g volume) :
    eLpNorm g 3 volume ≤ (eLpNorm g 2 volume) ^ (1 / 2 : ℝ) *
      (eLpNorm g 6 volume) ^ (1 / 2 : ℝ) := by
  have h := ENNReal.lintegral_mul_norm_pow_le
    (hg.enorm.pow_const (2 : ℝ)) (hg.enorm.pow_const (6 : ℝ))
    (p := (3 / 4 : ℝ)) (q := (1 / 4 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  have he : (fun x => (‖g x‖ₑ ^ (2 : ℝ)) ^ (3 / 4 : ℝ) *
      (‖g x‖ₑ ^ (6 : ℝ)) ^ (1 / 4 : ℝ)) = fun x => ‖g x‖ₑ ^ (3 : ℝ) := by
    funext x
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  rw [he] at h
  have hh := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 1 / 3)
  simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 3),
    ← ENNReal.rpow_mul] at hh
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (3 : ℝ≥0∞) ≠ 0)
    (by norm_num : (3 : ℝ≥0∞) ≠ ⊤),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (6 : ℝ≥0∞) ≠ 0)
    (by norm_num : (6 : ℝ≥0∞) ≠ ⊤), ENNReal.toReal_ofNat, ← ENNReal.rpow_mul]
  convert hh using 1 <;> norm_num

/-- Velocity Sobolev embedding with the same generous constant as A05. -/
theorem velocity_six_le_gradient_two (z : Space → Space) (hz : SmoothL2 z) :
    eLpNorm z 6 volume ≤ ENNReal.ofReal gradientL6Const * eLpNorm (gradTensor z) 2 volume := by
  have hd : eLpNorm (fderiv ℝ z) 2 volume ≤ 3 * eLpNorm (gradTensor z) 2 volume := by
    calc
      _ ≤ ∑ i : Fin 3, eLpNorm (dirDeriv i z) 2 volume :=
        A05.eLpNorm_le_sum_of_norm_le (by norm_num)
          (fun i => (hz.dir i).memLp.aestronglyMeasurable)
          (fun x => A05.opNorm_le_sum (fderiv ℝ z x))
      _ ≤ ∑ _i : Fin 3, eLpNorm (gradTensor z) 2 volume := by
        apply Finset.sum_le_sum
        intro i _
        exact eLpNorm_mono (fun x => PiLp.norm_apply_le (gradTensor z x) i)
      _ = _ := by simp [Finset.sum_const]
  have hv := NavierStokesR3.RieszTestOperators.smooth_eLpNorm_six_le
    (hz.contDiff.of_le (by simp)) hz.memLp
  refine hv.trans ((mul_le_mul' le_rfl hd).trans ?_)
  rw [← mul_assoc]
  gcongr
  rw [← ENNReal.ofReal_coe_nnreal]
  have h3 : (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) := by norm_num
  rw [h3, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  unfold A05.gradientL6Const
  have hc := (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Space) 2).coe_nonneg
  linarith

/-- General convection interpolation in physical extended norms; no critical gate. -/
theorem convection_interpolation (z : Space → Space) (hz : SmoothL2 z) :
    ENNReal.ofReal |advectionWork z| ≤
      (ENNReal.ofReal gradientL6Const) ^ (3 / 2 : ℝ) *
        (eLpNorm (gradTensor z) 2 volume) ^ (3 / 2 : ℝ) *
        (eLpNorm (lap z) 2 volume) ^ (3 / 2 : ℝ) := by
  have hcg : Continuous (gradTensor z) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin 3 => Space)).comp
      (continuous_pi fun j => (hz.dir j).contDiff.continuous)
  have hg := (eLpNorm_three_interpolation (gradTensor z) hcg.aestronglyMeasurable).trans
    (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (A05.eLpNorm_gradTensor_six_le hz)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)))
  have hw : ENNReal.ofReal |advectionWork z| ≤
      eLpNorm z 6 volume * eLpNorm (gradTensor z) 3 volume * eLpNorm (lap z) 2 volume := by
    rw [← Real.enorm_eq_ofReal_abs]
    exact (enorm_integral_le_lintegral_enorm _).trans (lintegral_convection_holder_632 z hz)
  refine hw.trans ((mul_le_mul' (mul_le_mul' (velocity_six_le_gradient_two z hz) hg) le_rfl).trans_eq ?_)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hp (x : ℝ≥0∞) : x * x ^ (1 / 2 : ℝ) = x ^ (3 / 2 : ℝ) := by
    conv_lhs => lhs; rw [← ENNReal.rpow_one x]
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  calc
    _ = (ENNReal.ofReal gradientL6Const * (ENNReal.ofReal gradientL6Const) ^ (1 / 2 : ℝ)) *
        (eLpNorm (gradTensor z) 2 volume * (eLpNorm (gradTensor z) 2 volume) ^ (1 / 2 : ℝ)) *
        (eLpNorm (lap z) 2 volume * (eLpNorm (lap z) 2 volume) ^ (1 / 2 : ℝ)) := by ring
    _ = _ := by rw [hp, hp, hp]

end NSFormalization.Section4.A04
