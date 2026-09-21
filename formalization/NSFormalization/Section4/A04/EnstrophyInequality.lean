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

/-- Elementary scaled quartic Young estimate, also valid at zero. -/
theorem young_quartic {a b ε : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hε : 0 < ε) :
    a * b ^ 3 ≤ ε * b ^ 4 + a ^ 4 / ε ^ 3 := by
  by_cases h : b ≤ a / ε
  · have hh : a * b ^ 3 ≤ a * (a / ε) ^ 3 := by gcongr
    have he : a * (a / ε) ^ 3 = a ^ 4 / ε ^ 3 := by ring
    rw [he] at hh
    exact hh.trans (le_add_of_nonneg_left (by positivity))
  · have hh : a ≤ ε * b := by
      have := (div_lt_iff₀ hε).mp (lt_of_not_ge h)
      linarith
    have hm := mul_le_mul_of_nonneg_right hh (pow_nonneg hb 3)
    have he : ε * b * b ^ 3 = ε * b ^ 4 := by ring
    rw [he] at hm
    exact hm.trans (le_add_of_nonneg_right (by positivity))

/-- Real-valued convection bound from explicit B0 physical-norm bounds.
The two hypotheses concern only norm carriers, not convection or absorption. -/
theorem convection_bound_of_norm_bridges (z : Space → Space) (hz : SmoothL2 z)
    {H D : ℝ} (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hG : eLpNorm (gradTensor z) 2 volume ≤ ENNReal.ofReal H)
    (hL : eLpNorm (lap z) 2 volume ≤ ENNReal.ofReal D) :
    |advectionWork z| ≤ gradientL6Const ^ (3 / 2 : ℝ) *
      H ^ (3 / 2 : ℝ) * D ^ (3 / 2 : ℝ) := by
  have hC := A05.gradientL6Const_pos
  have h := (convection_interpolation z hz).trans
    (mul_le_mul' (mul_le_mul' le_rfl
      (ENNReal.rpow_le_rpow hG (by norm_num)))
      (ENNReal.rpow_le_rpow hL (by norm_num)))
  rw [ENNReal.ofReal_rpow_of_nonneg A05.gradientL6Const_pos.le (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg hH (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg hD (by norm_num),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

/-- Young absorption for the squared-norm exponents, with an explicit coefficient. -/
theorem young_three_quarters {C Y Z ε : ℝ} (hC : 0 ≤ C) (hY : 0 ≤ Y)
    (hZ : 0 ≤ Z) (hε : 0 < ε) :
    C * Y ^ (3 / 4 : ℝ) * Z ^ (3 / 4 : ℝ) ≤
      ε * Z + C ^ 4 / ε ^ 3 * Y ^ 3 := by
  have h := young_quartic (a := C * Y ^ (3 / 4 : ℝ))
    (b := Z ^ (1 / 4 : ℝ)) (by positivity) (by positivity) hε
  have h3 : (Z ^ (1 / 4 : ℝ)) ^ (3 : ℕ) = Z ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hZ]; norm_num
  have h4 : (Z ^ (1 / 4 : ℝ)) ^ (4 : ℕ) = Z := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hZ]; norm_num
  have hY4 : (Y ^ (3 / 4 : ℝ)) ^ (4 : ℕ) = Y ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hY]; norm_num
  rw [h3, h4, mul_pow, hY4] at h
  convert h using 1 <;> ring

/-- Quadratic force absorption with arbitrary positive scale. -/
theorem young_two_factors {a b ε : ℝ} (hε : 0 < ε) :
    2 * a * b ≤ ε * b ^ 2 + a ^ 2 / ε := by
  have h : 2 * a * b ≤ (ε ^ 2 * b ^ 2 + a ^ 2) / ε :=
    (le_div_iff₀ hε).2 (by nlinarith [sq_nonneg (ε * b - a)])
  convert h using 1 <;> field_simp

/-- Weighted inhomogeneous identity. The weight permits the registered Fourier
normalization to be supplied by B0 without asserting a false unweighted equality. -/
theorem weightedEnergyIdentity
    {ν T : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField}
    (w : A02.ClassicalSolutionR ν a f T) (hf : A02.MemForceR f) (κ : ℝ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt
      (fun s => l2Sq (slice w.velocity s) + κ * gradientSq (slice w.velocity s))
      (-2 * ν * gradientSq (slice w.velocity t) - 2 * κ * ν * laplacianSq (slice w.velocity t) +
        2 * κ * advectionWork (slice w.velocity t) +
        2 * pairing (slice w.velocity t) (slice f t) -
        2 * κ * pairing (slice f t) (A05.lap (slice w.velocity t))) t := by
  have h := (energyIdentity_l2Sq w hf ht).add
    ((enstrophyIdentity_gradientSq w hf ht).const_mul κ)
  convert h using 1 <;> first | rfl | (simp only [gradientSq]; ring)

/-- Cauchy–Schwarz on carrier B, with physical integral norms. -/
theorem abs_pairing_carrier_le
    (A B : EulerLpTranslation.SmoothL2Field Space) :
    |pairing A.field B.field| ≤ Real.sqrt (l2Sq A.field) * Real.sqrt (l2Sq B.field) := by
  have hn (W : EulerLpTranslation.SmoothL2Field Space) :
      Real.sqrt (l2Sq W.field) = ‖W.toLp‖ := by
    change Real.sqrt (∫ x, ‖W.field x‖ ^ 2) = _
    rw [← norm_toLp_sq_eq_l2Sq, Real.sqrt_sq (norm_nonneg _)]
  rw [hn A, hn B]
  change |∫ x, inner ℝ (A.field x) (B.field x)| ≤ _
  rw [pairing_eq_inner]
  exact abs_real_inner_le_norm _ _

/-- General cubic absorption, retaining the low-order H² term U. -/
theorem weighted_cubic_assembly {ν κ C U G L F N P Q d Y Z : ℝ}
    (hν : 0 < ν) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hC : 0 ≤ C)
    (hU : 0 ≤ U) (hG : 0 ≤ G) (hL : 0 ≤ L) (hF : 0 ≤ F)
    (hY : Y = U + κ * G) (hZ : Z ≤ U + 2 * κ * G + κ ^ 2 * L)
    (hd : d = -2 * ν * G - 2 * κ * ν * L + 2 * κ * N + 2 * P - 2 * κ * Q)
    (hN : |N| ≤ C * G ^ (3 / 4 : ℝ) * L ^ (3 / 4 : ℝ))
    (hP : P ≤ Real.sqrt U * Real.sqrt F)
    (hQ : -Q ≤ Real.sqrt F * Real.sqrt L) :
    d + ν * Z ≤
      ((2 * κ * C) ^ 4 / (κ * ν / 2) ^ 3 / κ ^ 3 + (1 + ν)) * (1 + Y) ^ 3 +
        (1 + 2 * κ / ν) * F := by
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  have hn := young_three_quarters (C := 2 * κ * C) (Y := G) (Z := L)
    (by positivity) hG hL (show 0 < κ * ν / 2 by positivity)
  have hn' : 2 * κ * N ≤ κ * ν / 2 * L +
      (2 * κ * C) ^ 4 / (κ * ν / 2) ^ 3 * G ^ 3 := by
    have h := mul_le_mul_of_nonneg_left ((le_abs_self N).trans hN) (by positivity : 0 ≤ 2 * κ)
    nlinarith only [h, hn]
  have hp : 2 * P ≤ U + F := by
    have h := young_two_factors (a := Real.sqrt U) (b := Real.sqrt F) (ε := 1) (by norm_num)
    rw [Real.sq_sqrt hU, Real.sq_sqrt hF] at h
    nlinarith
  have hq : -2 * κ * Q ≤ κ * ν / 2 * L + (2 * κ / ν) * F := by
    have h := young_two_factors (a := Real.sqrt F) (b := Real.sqrt L)
      (ε := ν / 2) (by positivity)
    rw [Real.sq_sqrt hL, Real.sq_sqrt hF] at h
    have hh := mul_le_mul_of_nonneg_left h hκ.le
    have hqq := mul_le_mul_of_nonneg_left hQ (show 0 ≤ 2 * κ by positivity)
    have he : κ * (ν / 2 * L + F / (ν / 2)) = κ * ν / 2 * L + (2 * κ / ν) * F := by ring
    rw [he] at hh
    nlinarith only [hh, hqq]
  have hGY : G ≤ Y / κ := (le_div_iff₀ hκ).2 (by rw [hY]; nlinarith)
  have hcube : G ^ 3 ≤ Y ^ 3 / κ ^ 3 := by
    calc G ^ 3 ≤ (Y / κ) ^ 3 := by gcongr
         _ = _ := by ring
  have hcoef : 0 ≤ (2 * κ * C) ^ 4 / (κ * ν / 2) ^ 3 := by positivity
  have hbound := mul_le_mul_of_nonneg_left hcube hcoef
  have hmono : Y ^ 3 ≤ (1 + Y) ^ 3 := by gcongr; linarith
  have hmono1 : Y ≤ (1 + Y) ^ 3 := by nlinarith [sq_nonneg Y, pow_nonneg hY0 3]
  have hc : 0 ≤ (2 * κ * C) ^ 4 / (κ * ν / 2) ^ 3 / κ ^ 3 := by positivity
  have hmajor := mul_le_mul_of_nonneg_left hmono hc
  have hmajor1 := mul_le_mul_of_nonneg_left hmono1 (show 0 ≤ 1 + ν by positivity)
  have hz := mul_le_mul_of_nonneg_left hZ hν.le
  have hk : κ ^ 2 ≤ κ := by nlinarith
  have hkL := mul_le_mul_of_nonneg_right hk hL
  have hkg := mul_le_mul_of_nonneg_right hκ1 hG
  have hdis : ν * (2 * κ * G + κ ^ 2 * L) ≤ 2 * ν * G + κ * ν * L := by
    nlinarith [mul_le_mul_of_nonneg_left hkL hν.le, mul_le_mul_of_nonneg_left hkg hν.le]
  have hUY : U ≤ Y := by rw [hY]; nlinarith [mul_nonneg hκ.le hG]
  have hu := mul_le_mul_of_nonneg_left hUY (show 0 ≤ 1 + ν by positivity)
  have he : (2 * κ * C) ^ 4 / (κ * ν / 2) ^ 3 * (Y ^ 3 / κ ^ 3) =
      ((2 * κ * C) ^ 4 / (κ * ν / 2) ^ 3 / κ ^ 3) * Y ^ 3 := by ring
  rw [he] at hbound
  nlinarith only [hn', hp, hq, hbound, hmajor, hmajor1, hz, hdis, hu, hd]

/-- The registered squared H¹ norm satisfies the cubic inequality, conditional
only on the displayed B0 norm bridges. The weight κ is fixed by the Fourier
convention; this theorem allows any 0<κ≤1. No differential or nonlinear bound
is assumed. -/
theorem enstrophy_differential_of_norm_bridges
    {ν T κ : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField}
    (w : A02.ClassicalSolutionR ν a f T) (hf : A02.MemForceR f)
    (hν : 0 < ν) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hOne : ∀ s ∈ Ioo (0 : ℝ) T,
      (D01.sobolevENorm 1 (slice w.velocity s)).toReal ^ 2 =
        l2Sq (slice w.velocity s) + κ * gradientSq (slice w.velocity s))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T)
    (hTwo : (D01.sobolevENorm 2 (slice w.velocity t)).toReal ^ 2 ≤
      l2Sq (slice w.velocity t) + 2 * κ * gradientSq (slice w.velocity t) +
        κ ^ 2 * laplacianSq (slice w.velocity t))
    (hGradient : eLpNorm (gradTensor (slice w.velocity t)) 2 volume ≤
      ENNReal.ofReal (Real.sqrt (gradientSq (slice w.velocity t)))) :
    deriv (fun s => (D01.sobolevENorm 1 (slice w.velocity s)).toReal ^ 2) t +
        ν * (D01.sobolevENorm 2 (slice w.velocity t)).toReal ^ 2 ≤
      ((2 * κ * gradientL6Const ^ (3 / 2 : ℝ)) ^ 4 / (κ * ν / 2) ^ 3 / κ ^ 3 + (1 + ν)) *
        (1 + (D01.sobolevENorm 1 (slice w.velocity t)).toReal ^ 2) ^ 3 +
      (1 + 2 * κ / ν) * l2Sq (slice f t) := by
  have hz : SmoothL2 (slice w.velocity t) := velocity_slice_smoothL2 w (Ioo_subset_Ico_self ht)
  have hG := gradientSq_nonneg (slice w.velocity t)
  have hL : 0 ≤ laplacianSq (slice w.velocity t) := integral_nonneg fun x => sq_nonneg _
  have hmem : MemLp (lap (slice w.velocity t)) 2 volume :=
    memLp_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ => ((hz.dir i).dir i).memLp)
  have hint : Integrable (fun x => ‖lap (slice w.velocity t) x‖ ^ 2) volume := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      hmem.integrable_norm_rpow (by norm_num) (by norm_num)
  have hLap : eLpNorm (lap (slice w.velocity t)) 2 volume =
      ENNReal.ofReal (Real.sqrt (laplacianSq (slice w.velocity t))) :=
    I02.eLpNorm_two_eq_ofReal_sqrt hint
  have hconv := convection_bound_of_norm_bridges (slice w.velocity t) hz
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hGradient hLap.le
  have hsqrt (x : ℝ) (hx : 0 ≤ x) :
      (Real.sqrt x) ^ (3 / 2 : ℝ) = x ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]; norm_num
  rw [hsqrt _ hG, hsqrt _ hL] at hconv
  have hP := abs_pairing_carrier_le
    (velocitySliceField w (Ioo_subset_Ico_self ht)) (forceSliceField hf ht.1.le)
  have hQ := abs_pairing_carrier_le (forceSliceField hf ht.1.le)
    (NSFormalization.Source.OrdinaryViscousStability.laplacianField (velocitySliceField w (Ioo_subset_Ico_self ht)))
  have hlapfield :
      (NSFormalization.Source.OrdinaryViscousStability.laplacianField
        (velocitySliceField w (Ioo_subset_Ico_self ht))).field = lap (slice w.velocity t) := by
    funext x
    rw [laplacianField_velocitySlice_field w (Ioo_subset_Ico_self ht) x]
    rfl
  rw [hlapfield] at hQ
  change |pairing (slice w.velocity t) (slice f t)| ≤
    Real.sqrt (l2Sq (slice w.velocity t)) * Real.sqrt (l2Sq (slice f t)) at hP
  change |pairing (slice f t) (lap (slice w.velocity t))| ≤
    Real.sqrt (l2Sq (slice f t)) * Real.sqrt (laplacianSq (slice w.velocity t)) at hQ
  have hd := weightedEnergyIdentity w hf κ ht
  have hdNorm : HasDerivAt
      (fun s => (D01.sobolevENorm 1 (slice w.velocity s)).toReal ^ 2)
      (-2 * ν * gradientSq (slice w.velocity t) - 2 * κ * ν * laplacianSq (slice w.velocity t) +
        2 * κ * advectionWork (slice w.velocity t) +
        2 * pairing (slice w.velocity t) (slice f t) -
        2 * κ * pairing (slice f t) (lap (slice w.velocity t))) t := by
    apply hd.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hOne s hs
  exact weighted_cubic_assembly hν hκ hκ1 (Real.rpow_nonneg A05.gradientL6Const_pos.le _)
    (l2Sq_nonneg _) hG hL (l2Sq_nonneg _) (hOne t ht) hTwo hdNorm.deriv hconv
    ((le_abs_self _).trans hP) ((neg_le_abs _).trans hQ)

/-- Fixed Fourier convention κ=(2π)⁻². With c=1 and
Cν=(2κ C₀^(3/2))⁴/(κν/2)³/κ³ + (1+ν) + (1+2κ/ν), where
C₀=A05.gradientL6Const, the coefficient depends only on ν and universal
normalization constants. All B0 obligations are displayed as norm identities
or inequalities. -/
theorem enstrophy_differential
    {ν T : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField}
    (w : A02.ClassicalSolutionR ν a f T) (hf : A02.MemForceR f) (hν : 0 < ν)
    (hOne : ∀ s ∈ Ioo (0 : ℝ) T,
      (D01.sobolevENorm 1 (slice w.velocity s)).toReal ^ 2 =
        l2Sq (slice w.velocity s) + (1 / (2 * Real.pi) ^ 2) * gradientSq (slice w.velocity s))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T)
    (hTwo : (D01.sobolevENorm 2 (slice w.velocity t)).toReal ^ 2 ≤
      l2Sq (slice w.velocity t) + 2 * (1 / (2 * Real.pi) ^ 2) * gradientSq (slice w.velocity t) +
        (1 / (2 * Real.pi) ^ 2) ^ 2 * laplacianSq (slice w.velocity t))
    (hGradient : eLpNorm (gradTensor (slice w.velocity t)) 2 volume ≤
      ENNReal.ofReal (Real.sqrt (gradientSq (slice w.velocity t)))) :
    let κ := 1 / (2 * Real.pi) ^ 2
    let Cν := (2 * κ * gradientL6Const ^ (3 / 2 : ℝ)) ^ 4 / (κ * ν / 2) ^ 3 / κ ^ 3 +
      (1 + ν) + (1 + 2 * κ / ν)
    deriv (fun s => (D01.sobolevENorm 1 (slice w.velocity s)).toReal ^ 2) t +
        ν * (D01.sobolevENorm 2 (slice w.velocity t)).toReal ^ 2 ≤
      Cν * (1 + (D01.sobolevENorm 1 (slice w.velocity t)).toReal ^ 2) ^ 3 +
        Cν * l2Sq (slice f t) := by
  let κ := 1 / (2 * Real.pi) ^ 2
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hκ1 : κ ≤ 1 := by
    dsimp [κ]
    apply (div_le_one (by positivity)).2
    nlinarith [Real.pi_gt_three]
  have h := enstrophy_differential_of_norm_bridges w hf hν hκ hκ1 hOne ht hTwo hGradient
  dsimp only
  have hA : 0 ≤ (2 * κ * gradientL6Const ^ (3 / 2 : ℝ)) ^ 4 / (κ * ν / 2) ^ 3 / κ ^ 3 + (1 + ν) := by positivity
  have hB : 0 ≤ 1 + 2 * κ / ν := by positivity
  have hY : 0 ≤ (1 + (D01.sobolevENorm 1 (slice w.velocity t)).toReal ^ 2) ^ 3 := by positivity
  have hF := l2Sq_nonneg (slice f t)
  nlinarith only [h, mul_nonneg hA hF, mul_nonneg hB hY]

/-- The requested H¹/H² convection estimate in registered norm vocabulary.
Only the two Fourier-to-physical norm bridges are hypotheses; their explicit
2π factors match the Fourier weight 1+|ξ|². -/
theorem convection_sobolev (z : Space → Space) (hz : SmoothL2 z)
    (hG : eLpNorm (gradTensor z) 2 volume ≤
      ENNReal.ofReal ((2 * Real.pi) * (D01.sobolevENorm 1 z).toReal))
    (hL : eLpNorm (lap z) 2 volume ≤
      ENNReal.ofReal ((2 * Real.pi) ^ 2 * (D01.sobolevENorm 2 z).toReal)) :
    |advectionWork z| ≤
      (gradientL6Const ^ (3 / 2 : ℝ) * (2 * Real.pi) ^ (3 / 2 : ℝ) *
        ((2 * Real.pi) ^ 2) ^ (3 / 2 : ℝ)) *
      (D01.sobolevENorm 1 z).toReal ^ (3 / 2 : ℝ) *
      (D01.sobolevENorm 2 z).toReal ^ (3 / 2 : ℝ) := by
  have h := convection_bound_of_norm_bridges z hz (by positivity) (by positivity) hG hL
  rw [Real.mul_rpow (by positivity) ENNReal.toReal_nonneg,
    Real.mul_rpow (by positivity) ENNReal.toReal_nonneg] at h
  convert h using 1 <;> ring

/-- The cubic estimate on every closed subinterval strictly inside (0,T).
The same ν-dependent constant works at every time in the interval. -/
theorem enstrophy_differential_on_Icc
    {ν T r s : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField}
    (w : A02.ClassicalSolutionR ν a f T) (hf : A02.MemForceR f) (hν : 0 < ν)
    (hr : 0 < r) (hs : s < T)
    (hOne : ∀ q ∈ Ioo (0 : ℝ) T,
      (D01.sobolevENorm 1 (slice w.velocity q)).toReal ^ 2 =
        l2Sq (slice w.velocity q) + (1 / (2 * Real.pi) ^ 2) * gradientSq (slice w.velocity q))
    (hTwo : ∀ t ∈ Icc r s, (D01.sobolevENorm 2 (slice w.velocity t)).toReal ^ 2 ≤
      l2Sq (slice w.velocity t) + 2 * (1 / (2 * Real.pi) ^ 2) * gradientSq (slice w.velocity t) +
        (1 / (2 * Real.pi) ^ 2) ^ 2 * laplacianSq (slice w.velocity t))
    (hGradient : ∀ t ∈ Icc r s, eLpNorm (gradTensor (slice w.velocity t)) 2 volume ≤
      ENNReal.ofReal (Real.sqrt (gradientSq (slice w.velocity t)))) :
    ∀ t ∈ Icc r s,
    let κ := 1 / (2 * Real.pi) ^ 2
    let Cν := (2 * κ * gradientL6Const ^ (3 / 2 : ℝ)) ^ 4 / (κ * ν / 2) ^ 3 / κ ^ 3 +
      (1 + ν) + (1 + 2 * κ / ν)
    deriv (fun q => (D01.sobolevENorm 1 (slice w.velocity q)).toReal ^ 2) t +
        ν * (D01.sobolevENorm 2 (slice w.velocity t)).toReal ^ 2 ≤
      Cν * (1 + (D01.sobolevENorm 1 (slice w.velocity t)).toReal ^ 2) ^ 3 +
        Cν * l2Sq (slice f t) := by
  intro t ht
  exact enstrophy_differential w hf hν hOne ⟨hr.trans_le ht.1, ht.2.trans_lt hs⟩
    (hTwo t ht) (hGradient t ht)

end NSFormalization.Section4.A04
