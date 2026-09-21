import NSFormalization.Paper1.CorrectionVectorNorms
import NSFormalization.Paper1.CorrectionEnergy
import NSFormalization.Source.InsertionFamily
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Actual presingular insertion energy norm

All time norms and gradient integrals are restricted to the open interval
(0,T). The totalized packet at and after its singular time is never included.
-/
noncomputable section
namespace NSFormalization.Paper1.InsertionEnergy
open NavierStokes NavierStokes.ProblemStatement NavierStokesR3.CompactEnergy
open Set MeasureTheory Filter Topology
open Source Source.PacketScaling CorrectionProfile CorrectionEnergy CorrectionForceNorms
open scoped ContDiff ENNReal

def velocityL2 (F : VelocityField) (t : ℝ) : ℝ := Real.sqrt (l2Sq F t)

def gradientL2 (F : VelocityField) (t : ℝ) : ℝ := Real.sqrt (dissipation F t)

/-- The ordinary squared spacetime L² norm of the full spatial gradient.
`dissipation` is the sum of the three genuine directional-gradient integrals. -/
def gradientSquare (T : ℝ) (F : VelocityField) : ℝ :=
  ∫ t in Ioo (0 : ℝ) T, dissipation F t

/-- The manuscript's L∞_t L²_x plus L²_{t,x} gradient norm on (0,T). -/
def energyNorm (T : ℝ) (F : VelocityField) : ℝ :=
  (eLpNorm (velocityL2 F) (⊤ : ℝ≥0∞) (volume.restrict (Ioo (0 : ℝ) T))).toReal +
    Real.sqrt (gradientSquare T F)

theorem energyNorm_nonneg (T : ℝ) (F : VelocityField) : 0 ≤ energyNorm T F :=
  add_nonneg ENNReal.toReal_nonneg (Real.sqrt_nonneg _)

theorem spatial_smooth {I : Set ℝ} {F : VelocityField}
    (hF : ContDiffOn ℝ ∞ F (I ×ˢ univ)) {t : ℝ} (ht : t ∈ I) :
    ContDiff ℝ ∞ (fun x => F (t, x)) := by
  apply contDiffOn_univ.mp
  exact hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun x _ => ⟨ht, mem_univ x⟩)

theorem l2Sq_continuousOn_interval {I : Set ℝ} {F : VelocityField} {K : Set Space}
    (hK : IsCompact K) (hF : ContDiffOn ℝ ∞ F (I ×ˢ univ))
    (hs : ∀ t ∈ I, tsupport (fun x => F (t, x)) ⊆ K) :
    ContinuousOn (l2Sq F) I := by
  apply continuousOn_integral_of_compact_support hK (hF.continuousOn.norm.pow 2)
  intro t x ht hx
  rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs t ht h))]
  simp

theorem dissipation_continuousOn_interval {I : Set ℝ} (hI : IsOpen I)
    {F : VelocityField} {K : Set Space} (hK : IsCompact K)
    (hF : ContDiffOn ℝ ∞ F (I ×ˢ univ))
    (hs : ∀ t ∈ I, tsupport (fun x => F (t, x)) ⊆ K) :
    ContinuousOn (dissipation F) I := by
  apply continuousOn_finsetSum
  intro i _
  have hd := (NavierStokes.ResidualRegularity.contDiffOn_spatialDerivative
    (hI.prod isOpen_univ) hF).clm_apply (contDiffOn_const (c := coordinateVector i))
  apply continuousOn_integral_of_compact_support hK (hd.continuousOn.norm.pow 2)
  intro t x ht hx
  have hn : x ∉ tsupport (fun y => F (t, y)) := fun h => hx (hs t ht h)
  change ‖fderiv ℝ (fun y => F (t, y)) x (coordinateVector i)‖ ^ 2 = 0
  simp only [fderiv_of_notMem_tsupport ℝ hn, zero_apply, norm_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]

theorem spatial_square_integrable {I : Set ℝ} {F : VelocityField} {K : Set Space}
    (hK : IsCompact K) (hF : ContDiffOn ℝ ∞ F (I ×ˢ univ))
    (hs : ∀ t ∈ I, tsupport (fun x => F (t, x)) ⊆ K) {t : ℝ} (ht : t ∈ I) :
    Integrable (fun x => ‖F (t, x)‖ ^ 2) := by
  exact integrable_norm_sq (spatial_smooth hF ht).continuous (slice_compact hK (hs t ht))

theorem norm_add_sq_bound (a b : Space) : ‖a + b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have h := norm_add_le a b
  nlinarith [norm_nonneg (a + b), norm_nonneg a, norm_nonneg b, sq_nonneg (‖a‖ - ‖b‖)]

theorem spatial_energy_add_bound {f g : Space → Space}
    (hf : Integrable (fun x => ‖f x‖ ^ 2)) (hg : Integrable (fun x => ‖g x‖ ^ 2)) :
    (∫ x, ‖f x + g x‖ ^ 2) ≤ 2 * ((∫ x, ‖f x‖ ^ 2) + ∫ x, ‖g x‖ ^ 2) := by
  calc
    _ ≤ ∫ x, 2 * (‖f x‖ ^ 2 + ‖g x‖ ^ 2) :=
      integral_mono_of_nonneg (Eventually.of_forall (fun x => sq_nonneg _))
        ((hf.add hg).const_mul 2) (Eventually.of_forall fun x => norm_add_sq_bound _ _)
    _ = _ := by rw [integral_const_mul, integral_add hf hg]

theorem gradientNorm_eq_timeL2 {T : ℝ} {F : VelocityField}
    (hm : AEStronglyMeasurable (dissipation F) (volume.restrict (Ioo (0 : ℝ) T)))
    (hi : IntegrableOn (dissipation F) (Ioo (0 : ℝ) T)) :
    MemLp (gradientL2 F) 2 (volume.restrict (Ioo (0 : ℝ) T)) ∧
    (eLpNorm (gradientL2 F) 2 (volume.restrict (Ioo (0 : ℝ) T))).toReal =
      Real.sqrt (gradientSquare T F) := by
  have hms : AEStronglyMeasurable (gradientL2 F) (volume.restrict (Ioo (0 : ℝ) T)) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hm
  have hsq : (fun t => gradientL2 F t ^ 2) = dissipation F := by
    funext t
    exact Real.sq_sqrt (dissipation_nonneg F t)
  constructor
  · apply (memLp_two_iff_integrable_sq hms).mpr
    rw [hsq]
    exact hi
  · rw [toReal_eLpNorm hms, lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hms]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs, hsq, gradientSquare]
    rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]

theorem energyNorm_le_of_squared_bounds {T A D : ℝ} {F : VelocityField}
    (hm : AEStronglyMeasurable (velocityL2 F) (volume.restrict (Ioo (0 : ℝ) T)))
    (hb : ∀ t ∈ Ioo (0 : ℝ) T, l2Sq F t ≤ A)
    (hd : gradientSquare T F ≤ D) :
    MemLp (velocityL2 F) (⊤ : ℝ≥0∞) (volume.restrict (Ioo (0 : ℝ) T)) ∧
    energyNorm T F ≤ Real.sqrt A + Real.sqrt D := by
  have hbound : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) T), ‖velocityL2 F t‖ ≤ Real.sqrt A := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ velocityL2 F t from Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (hb t ht)
  have he : eLpNorm (velocityL2 F) (⊤ : ℝ≥0∞) (volume.restrict (Ioo (0 : ℝ) T)) ≤
      ENNReal.ofReal (Real.sqrt A) := eLpNormEssSup_le_of_ae_bound hbound
  refine ⟨⟨hm, he.trans_lt ENNReal.ofReal_lt_top⟩, ?_⟩
  apply add_le_add _ (Real.sqrt_le_sqrt hd)
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top he).trans_eq
    (ENNReal.toReal_ofReal (Real.sqrt_nonneg A))

theorem spatial_gradient_square_integrable {f : Space → Space} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (e : Space) :
    Integrable (fun x => ‖fderiv ℝ f x e‖ ^ 2) :=
  integrable_norm_sq
    (((hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous)
    (hc.fderiv_apply ℝ e)

theorem dissipation_add_bound {F G : VelocityField} {t : ℝ}
    (hF : ContDiff ℝ ∞ (fun x => F (t, x))) (hG : ContDiff ℝ ∞ (fun x => G (t, x)))
    (hcF : HasCompactSupport (fun x => F (t, x))) (hcG : HasCompactSupport (fun x => G (t, x))) :
    dissipation (fun z => F z + G z) t ≤ 2 * (dissipation F t + dissipation G t) := by
  unfold dissipation NavierStokes.PeriodicIntegration.spatialPartial
  simp_rw [fderiv_fun_add (hF.differentiable (by simp) _) (hG.differentiable (by simp) _),
    add_apply]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  exact (spatial_energy_add_bound (spatial_gradient_square_integrable hF hcF _)
    (spatial_gradient_square_integrable hG hcG _)).trans_eq (by ring)

theorem spatialDirection_eq_joint {F : VelocityField} (hF : ContDiff ℝ ∞ F)
    (t : ℝ) (x e : Space) :
    spatialDerivative F t x e = fderiv ℝ F (t, x) (0, e) := by
  have hi := (hasFDerivAt_const (𝕜 := ℝ) t x).prodMk (hasFDerivAt_id (𝕜 := ℝ) x)
  have hd := (((hF.differentiable (by simp)) (t, x)).hasFDerivAt.comp x hi).fderiv
  change fderiv ℝ (fun y => F (t, y)) x = _ at hd
  change fderiv ℝ (fun y => F (t, y)) x e = _
  rw [hd]
  simp

theorem compact_direction_time_integrable {F : VelocityField} (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (e : Space) :
    Integrable (fun t => ∫ x : Space, ‖spatialDerivative F t x e‖ ^ 2) := by
  have hd : Continuous (fun z : SpaceTime => fderiv ℝ F z (0, e)) :=
    ((hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have hdc : HasCompactSupport (fun z : SpaceTime => fderiv ℝ F z (0, e)) := hc.fderiv_apply ℝ _
  have hc2 : HasCompactSupport (fun z : SpaceTime => ‖fderiv ℝ F z (0, e)‖ ^ 2) := by
    simpa only [Function.comp_def] using
      hdc.comp_left (g := fun y : Space => ‖y‖ ^ 2)
        (by simp only [norm_zero, zero_pow (by decide : 2 ≠ 0)])
  have hi : Integrable (fun z : SpaceTime => ‖fderiv ℝ F z (0, e)‖ ^ 2) :=
    (hd.norm.pow 2).integrable_of_hasCompactSupport hc2
  simpa only [spatialDirection_eq_joint hF] using hi.integral_prod_left

theorem compact_dissipation_integrable {F : VelocityField} (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) : Integrable (dissipation F) := by
  apply integrable_finsetSum
  intro i _
  exact compact_direction_time_integrable hF hc (coordinateVector i)

/-- Full physical correction dissipation controls every restricted interval. -/
theorem correction_gradientSquare_bound {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Ioc (0 : ℝ) 1,
      IntegrableOn (dissipation (physicalCorrection v x₀ T θ η ε)) (Ioo (0 : ℝ) T) ∧
      gradientSquare T (physicalCorrection v x₀ T θ η ε) ≤ C * ε ^ 3 := by
  have hi (i : Fin 3) := physicalCorrection_total_direction_energy hv x₀ T hθ hη hθc hηc (coordinateVector i)
  choose C hC hb using hi
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), ?_⟩
  intro ε hε
  have hW := physicalCorrection_smooth hv x₀ T ε hθ hη
  have hcW := physicalCorrection_compact v x₀ T ε hε.1.ne' hθc hηc
  have hD := compact_dissipation_integrable hW hcW
  refine ⟨hD.integrableOn, ?_⟩
  calc
    _ ≤ ∫ t : ℝ, dissipation (physicalCorrection v x₀ T θ η ε) t :=
      setIntegral_le_integral hD (Eventually.of_forall (dissipation_nonneg _))
    _ = ∑ i : Fin 3, ∫ t : ℝ, ∫ x : Space,
        ‖spatialDerivative (physicalCorrection v x₀ T θ η ε) t x (coordinateVector i)‖ ^ 2 := by
      change (∫ t : ℝ, ∑ i : Fin 3, ∫ x : Space,
        ‖spatialDerivative (physicalCorrection v x₀ T θ η ε) t x (coordinateVector i)‖ ^ 2) = _
      rw [integral_finsetSum _ (fun i _ => compact_direction_time_integrable hW hcW _)]
    _ ≤ ∑ i : Fin 3, C i * ε ^ 3 := Finset.sum_le_sum (fun i _ => hb i ε hε)
    _ = _ := (Finset.sum_mul _ _ _).symm


/-- Explicit packet energy scale, with the actual spatial integrals. -/
theorem packet_l2_bound {u : VelocityField} {E T ε : ℝ} (hε : 0 < ε)
    (hE : ∀ s ∈ Ico (0 : ℝ) 1, l2Sq u s ≤ E) (x₀ : Space) :
    ∀ t ∈ Ioo (0 : ℝ) T,
      l2Sq (parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField u)) t ≤ ε * E := by
  intro t ht
  have hk : 0 < ε⁻¹ := inv_pos.mpr hε
  have hend : T - ε ^ 2 + ((ε⁻¹) ^ 2)⁻¹ = T := by simp
  by_cases hb : t ≤ T - ε ^ 2
  · have hz : ∀ x, parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField u) (t,x) = 0 :=
      fun x => zeroPast_dilate_early u ε⁻¹ ((ε⁻¹)^2) ε⁻¹ (T-ε^2)
        (sq_nonneg _) x₀ hb x
    have hE0 : 0 ≤ E := (integral_nonneg (fun x : Space => sq_nonneg ‖u (0, x)‖)).trans (hE 0 ⟨le_rfl, zero_lt_one⟩)
    simpa [l2Sq, hz] using mul_nonneg hε.le hE0
  · have ha := lt_of_not_ge hb
    have hs := reference_time_mem hk (t₀ := T - ε^2) (t := t)
      ⟨ha.le, by simpa only [hend] using ht.2⟩
    have hp : 0 < (ε⁻¹)^2 * (t - (T - ε^2)) :=
      mul_pos (sq_pos_of_pos hk) (sub_pos.mpr ha)
    rw [l2Sq_parabolic _ _ _ hk x₀ t, inv_inv]
    have heq : l2Sq (zeroPastField u) ((ε⁻¹)^2 * (t - (T-ε^2))) =
        l2Sq u ((ε⁻¹)^2 * (t - (T-ε^2))) := by
      simp only [l2Sq, zeroPastField_of_pos u hp]
    rw [heq]
    exact mul_le_mul_of_nonneg_left (hE _ hs) hε.le

theorem packet_gradientSquare {u : VelocityField} {T ε : ℝ}
    (hε : 0 < ε) (hT : 0 ≤ T) (hsmall : ε ^ 2 ≤ T)
    (hd : IntegrableOn (dissipation u) (Ioo (0 : ℝ) 1)) (x₀ : Space) :
    IntegrableOn (dissipation (parabolicVelocity ε⁻¹ (T-ε^2) x₀ (zeroPastField u)))
      (Ioo (0 : ℝ) T) ∧
    gradientSquare T (parabolicVelocity ε⁻¹ (T-ε^2) x₀ (zeroPastField u)) =
      ε * gradientSquare 1 u := by
  have hk : 0 < ε⁻¹ := inv_pos.mpr hε
  have ht₀ : 0 ≤ T - ε^2 := sub_nonneg.mpr hsmall
  have hend : T - ε ^ 2 + ((ε⁻¹) ^ 2)⁻¹ = T := by simp
  refine ⟨by simpa only [hend] using delayed_full_dissipation_integrable hk ht₀ x₀ hd, ?_⟩
  have he := total_delayed_dissipation hk ht₀ x₀ hd
  rw [hend, inv_inv, intervalIntegral.integral_of_le hT,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    integral_Ioc_eq_integral_Ioo] at he
  exact he


/-- A genuine energy-space estimate for a smooth compact perturbation split
into two fields. Integrability of both component gradients is explicit. -/
theorem energyNorm_add_estimate {T A B C D : ℝ} {F W U : VelocityField}
    {K : Set Space} (hK : IsCompact K)
    (hF : ContDiffOn ℝ ∞ F (Ioo (0 : ℝ) T ×ˢ univ))
    (hsF : ∀ t ∈ Ioo (0 : ℝ) T, tsupport (fun x => F (t,x)) ⊆ K)
    (hW : ContDiff ℝ ∞ W) (hcW : HasCompactSupport W)
    (heq : F = fun z => W z + U z)
    (hA : ∀ t ∈ Ioo (0 : ℝ) T, l2Sq W t ≤ A)
    (hB : ∀ t ∈ Ioo (0 : ℝ) T, l2Sq U t ≤ B)
    (hiW : IntegrableOn (dissipation W) (Ioo (0 : ℝ) T))
    (hiU : IntegrableOn (dissipation U) (Ioo (0 : ℝ) T))
    (hC : gradientSquare T W ≤ C) (hD : gradientSquare T U ≤ D) :
    MemLp (velocityL2 F) ⊤ (volume.restrict (Ioo (0 : ℝ) T)) ∧
    MemLp (gradientL2 F) 2 (volume.restrict (Ioo (0 : ℝ) T)) ∧
    energyNorm T F ≤ Real.sqrt (2 * (A+B)) + Real.sqrt (2 * (C+D)) := by
  have hUeq : U = fun z => F z - W z := by
    funext z
    rw [heq]
    exact (add_sub_cancel_left (W z) (U z)).symm
  have hcWs (t : ℝ) : HasCompactSupport (fun x => W (t,x)) := by
    apply HasCompactSupport.intro ((hcW : IsCompact (tsupport W)).image continuous_snd)
    intro x hx
    apply image_eq_zero_of_notMem_tsupport (f := W)
    intro htx
    exact hx ⟨(t,x), htx, rfl⟩
  have hWs (t : ℝ) : ContDiff ℝ ∞ (fun x => W (t,x)) :=
    hW.comp (contDiff_const.prodMk contDiff_id)
  have hcFs (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) : HasCompactSupport (fun x => F (t,x)) :=
    hK.of_isClosed_subset (isClosed_tsupport _) (hsF t ht)
  have hUs (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) : ContDiff ℝ ∞ (fun x => U (t,x)) := by
    rw [hUeq]
    exact (spatial_smooth hF ht).sub (hWs t)
  have hcUs (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) : HasCompactSupport (fun x => U (t,x)) := by
    rw [hUeq]
    exact (hcFs t ht).sub (hcWs t)
  have henergy (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) : l2Sq F t ≤ 2*(A+B) := by
    have hiWs : Integrable (fun x => ‖W (t,x)‖^2) :=
      integrable_norm_sq (hWs t).continuous (hcWs t)
    have hiUs : Integrable (fun x => ‖U (t,x)‖^2) :=
      integrable_norm_sq (hUs t ht).continuous (hcUs t ht)
    rw [heq]
    exact (spatial_energy_add_bound hiWs hiUs).trans
      (mul_le_mul_of_nonneg_left (add_le_add (hA t ht) (hB t ht)) (by norm_num))
  have hgrad (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
      dissipation F t ≤ 2*(dissipation W t + dissipation U t) := by
    rw [heq]
    exact dissipation_add_bound (hWs t) (hUs t ht) (hcWs t) (hcUs t ht)
  have hmD : AEStronglyMeasurable (dissipation F) (volume.restrict (Ioo (0 : ℝ) T)) :=
    (dissipation_continuousOn_interval isOpen_Ioo hK hF hsF).aestronglyMeasurable measurableSet_Ioo
  have hiMajor := (hiW.add hiU).const_mul 2
  have hgradAE : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) T),
      ‖dissipation F t‖ ≤ 2*(dissipation W t + dissipation U t) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (dissipation_nonneg F t)]
    exact hgrad t ht
  have hiF : IntegrableOn (dissipation F) (Ioo (0 : ℝ) T) := hiMajor.mono' hmD hgradAE
  have htotal : gradientSquare T F ≤ 2*(C+D) := by
    calc
      _ ≤ ∫ t in Ioo (0 : ℝ) T, 2*(dissipation W t + dissipation U t) :=
        integral_mono_ae hiF hiMajor (by
          filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
          exact hgrad t ht)
      _ = 2*(gradientSquare T W + gradientSquare T U) := by
        rw [integral_const_mul, integral_add hiW hiU]
        rfl
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hC hD) (by norm_num)
  have hmE : AEStronglyMeasurable (velocityL2 F) (volume.restrict (Ioo (0 : ℝ) T)) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable
      ((l2Sq_continuousOn_interval hK hF hsF).aestronglyMeasurable measurableSet_Ioo)
  obtain ⟨hLp, hbound⟩ := energyNorm_le_of_squared_bounds hmE henergy htotal
  exact ⟨hLp, (gradientNorm_eq_timeL2 hmD hiF).1, hbound⟩


def perturbation (u v : VelocityField) (x₀ : Space) (T : ℝ)
    (θ : Space → ℝ) (η : ℝ → ℝ) (ε : ℝ) : VelocityField := fun z =>
  Source.InsertionFamily.velocity u v x₀ T θ η ε z - v z

/-- Uniform estimates for the exact velocity inserted by `InsertionFamily`.
The compact smooth perturbation hypotheses are conclusions of its already
proved insertion theorem. No PDE existence or stability theorem is assumed. -/
theorem insertion_energy_bound {u v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (hE : NavierStokesR3.ProblemStatement.UniformFiniteEnergy (Ico (0 : ℝ) 1) u)
    (hd : IntegrableOn (dissipation u) (Ioo (0 : ℝ) 1))
    (x₀ : Space) {T : ℝ} (hT : 0 ≤ T) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) :
    ∃ A B C D : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ C ∧ 0 ≤ D ∧
      ∀ ε ∈ Ioc (0 : ℝ) 1, ε ^ 2 ≤ T →
      ∀ K : Set Space, IsCompact K →
      ContDiffOn ℝ ∞ (perturbation u v x₀ T θ η ε) (Ioo (0 : ℝ) T ×ˢ univ) →
      (∀ t ∈ Ioo (0 : ℝ) T, tsupport (fun x => perturbation u v x₀ T θ η ε (t,x)) ⊆ K) →
      MemLp (velocityL2 (perturbation u v x₀ T θ η ε)) ⊤ (volume.restrict (Ioo (0 : ℝ) T)) ∧
      MemLp (gradientL2 (perturbation u v x₀ T θ η ε)) 2 (volume.restrict (Ioo (0 : ℝ) T)) ∧
      energyNorm T (perturbation u v x₀ T θ η ε) ≤
        Real.sqrt (2*(A*ε^3+B*ε)) + Real.sqrt (2*(C*ε^3+D*ε)) := by
  obtain ⟨A, hA, hAb⟩ := physicalCorrection_uniform_energy hv x₀ T hθ hη hθc hηc
  obtain ⟨C, hC, hCb⟩ := correction_gradientSquare_bound hv x₀ T hθ hη hθc hηc
  obtain ⟨E, hE0, hEb⟩ := hE
  let D := gradientSquare 1 u
  have hD0 : 0 ≤ D := integral_nonneg (dissipation_nonneg u)
  refine ⟨A, 2*E, C, D, hA, mul_nonneg (by norm_num) hE0, hC, hD0, ?_⟩
  intro ε hε hsmall K hK hF hsF
  have hpE : ∀ s ∈ Ico (0 : ℝ) 1, l2Sq u s ≤ 2*E := by
    intro s hs
    have hb := (hEb s hs).2
    change (1/2 : ℝ)*l2Sq u s ≤ E at hb
    linarith
  have hpD := packet_gradientSquare hε.1 hT hsmall hd x₀
  have hcD := hCb ε hε
  have heq : perturbation u v x₀ T θ η ε = fun z =>
      physicalCorrection v x₀ T θ η ε z +
        parabolicVelocity ε⁻¹ (T-ε^2) x₀ (zeroPastField u) z := by
    funext z
    simp only [perturbation, Source.InsertionFamily.velocity, add_assoc, add_sub_cancel_left]
  exact energyNorm_add_estimate hK hF hsF
    (physicalCorrection_smooth hv x₀ T ε hθ hη)
    (physicalCorrection_compact v x₀ T ε hε.1.ne' hθc hηc) heq
    (fun t _ => hAb ε hε t)
    (fun t ht => (packet_l2_bound hε.1 hpE x₀ t ht).trans_eq (mul_comm _ _))
    hcD.1 hpD.1 hcD.2 (le_of_eq (hpD.2.trans (mul_comm _ _)))


/-- Vanishing in the actual energy norm for the same insertion family.
The only family hypothesis is eventual smooth compactness, already supplied
by `InsertionProperties`; the quantitative energy bounds are proved above. -/
theorem insertion_energy_tendsto_zero {u v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (hE : NavierStokesR3.ProblemStatement.UniformFiniteEnergy (Ico (0 : ℝ) 1) u)
    (hd : IntegrableOn (dissipation u) (Ioo (0 : ℝ) 1))
    (x₀ : Space) {T : ℝ} (hT : 0 < T) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hreg : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ K : Set Space, IsCompact K ∧
      ContDiffOn ℝ ∞ (perturbation u v x₀ T θ η ε) (Ioo (0 : ℝ) T ×ˢ univ) ∧
      ∀ t ∈ Ioo (0 : ℝ) T, tsupport (fun x => perturbation u v x₀ T θ η ε (t,x)) ⊆ K) :
    Tendsto (fun ε => energyNorm T (perturbation u v x₀ T θ η ε)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨A,B,C,D,hA,hB,hC,hD,hbound⟩ :=
    insertion_energy_bound hv hE hd x₀ hT.le hθ hη hθc hηc
  have heps : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioc (0 : ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with ε hp hu
    exact ⟨hp, hu.le⟩
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε^2 ≤ T := by
    have hh : Tendsto (fun ε : ℝ => ε^2) (𝓝[>] 0) (𝓝 0) := by
      have hc : Continuous (fun ε : ℝ => ε^2) := by fun_prop
      simpa only [zero_pow (by decide : 2 ≠ 0)] using
        (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    exact (hh.eventually (eventually_lt_nhds hT)).mono (fun _ h => h.le)
  apply squeeze_zero' (Eventually.of_forall (fun ε => energyNorm_nonneg T _))
    (g := fun ε => Real.sqrt (2*(A*ε^3+B*ε)) + Real.sqrt (2*(C*ε^3+D*ε)))
  · filter_upwards [heps,hsmall,hreg] with ε hε hs hr
    obtain ⟨K,hK,hF,hsF⟩ := hr
    exact (hbound ε hε hs K hK hF hsF).2.2
  · have hc : Continuous (fun ε : ℝ =>
        Real.sqrt (2*(A*ε^3+B*ε)) + Real.sqrt (2*(C*ε^3+D*ε))) := by fun_prop
    simpa using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds


/-- The needed regularity is an existing conclusion of the same insertion
family; it is not an additional analytic assumption. -/
theorem perturbation_regular_of_properties {ν r T τ ε : ℝ} {u v g : VelocityField}
    {q Q : PressureField} {G : VelocityField} {x₀ : Space}
    {θ : Space → ℝ} {η : ℝ → ℝ} (hv : ContDiff ℝ ∞ v)
    (hprops : Source.InsertionFamily.InsertionProperties ν v q g x₀ r T τ
      (Source.InsertionFamily.velocity u v x₀ T θ η ε) Q G) :
    ∃ K : Set Space, IsCompact K ∧
      ContDiffOn ℝ ∞ (perturbation u v x₀ T θ η ε) (Ioo (0 : ℝ) T ×ˢ univ) ∧
      ∀ t ∈ Ioo (0 : ℝ) T, tsupport (fun x => perturbation u v x₀ T θ η ε (t,x)) ⊆ K := by
  rcases hprops with ⟨hV,_,_,_,_,⟨K,hK,_,hKs⟩,_⟩
  refine ⟨K,hK,?_,?_⟩
  · exact (hV.mono (fun z hz => ⟨⟨hz.1.1.le,hz.1.2⟩,hz.2⟩)).sub hv.contDiffOn
  · intro t ht
    exact (hKs t ⟨ht.1.le,ht.2⟩).1


/-- Local-reference version: smoothness of the reference is needed only on
its prescribed presingular slab. This works for an arbitrary inserted field. -/
theorem difference_regular_of_properties {ν r T τ : ℝ} {v V g G : VelocityField}
    {q Q : PressureField} {x₀ : Space}
    (hv : ContDiffOn ℝ ∞ v (Ico (0 : ℝ) T ×ˢ univ))
    (hprops : Source.InsertionFamily.InsertionProperties ν v q g x₀ r T τ V Q G) :
    ∃ K : Set Space, IsCompact K ∧
      ContDiffOn ℝ ∞ (fun z => V z - v z) (Ioo (0 : ℝ) T ×ˢ univ) ∧
      ∀ t ∈ Ioo (0 : ℝ) T, tsupport (fun x => V (t,x) - v (t,x)) ⊆ K := by
  rcases hprops with ⟨hV,_,_,_,_,⟨K,hK,_,hKs⟩,_⟩
  refine ⟨K,hK,?_,?_⟩
  · exact (hV.sub hv).mono (fun z hz => ⟨⟨hz.1.1.le,hz.1.2⟩,hz.2⟩)
  · intro t ht
    exact (hKs t ⟨ht.1.le,ht.2⟩).1

end NSFormalization.Paper1.InsertionEnergy
