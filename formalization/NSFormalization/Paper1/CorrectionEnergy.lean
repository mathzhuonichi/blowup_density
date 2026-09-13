import NSFormalization.Paper1.CorrectionForceProfile
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Actual spatial energy of the compact background correction. -/
noncomputable section
namespace NSFormalization.Paper1.CorrectionEnergy
open NavierStokes NavierStokes.ProblemStatement Set MeasureTheory
open CorrectionProfile CorrectionForceProfile
open scoped ContDiff

theorem energy_dilate_translate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Space → E) (a ε : ℝ) (hε : 0 < ε) (x₀ : Space) :
    (∫ x : Space, ‖a • f (ε⁻¹ • (x - x₀))‖ ^ 2) =
      a ^ 2 * ε ^ 3 * (∫ x : Space, ‖f x‖ ^ 2) := by
  rw [integral_sub_right_eq_self (fun x : Space => ‖a • f (ε⁻¹ • x)‖ ^ 2) x₀]
  simp_rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [integral_const_mul,
    Measure.integral_comp_smul_of_nonneg volume (fun x : Space => ‖f x‖ ^ 2)
      ε⁻¹ (hR := (inv_pos.mpr hε).le)]
  simp [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul, mul_assoc]

theorem compact_energy_bound {E : Type*} [NormedAddCommGroup E]
    (f : Space → E) {K : Set Space} (hK : IsCompact K) (C : ℝ)
    (hb : ∀ x, ‖f x‖ ≤ C) (hs : ∀ x ∉ K, f x = 0) :
    (∫ x : Space, ‖f x‖ ^ 2) ≤ volume.real K * C ^ 2 := by
  have hg : Integrable (K.indicator (fun _ : Space => C ^ 2)) := by
    rw [integrable_indicator_iff hK.measurableSet]
    exact integrableOn_const hK.measure_ne_top
  calc
    _ ≤ ∫ x : Space, K.indicator (fun _ => C ^ 2) x := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _) hg
      apply Filter.Eventually.of_forall
      intro x
      by_cases hx : x ∈ K
      · simpa [hx] using pow_le_pow_left₀ (norm_nonneg (f x)) (hb x) 2
      · simp [hx, hs x hx]
    _ = _ := by rw [integral_indicator_const _ hK.measurableSet]; rfl

/-- The exact ε³ spatial-energy factor of the actual correction. -/
theorem physicalCorrection_energy {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T ε t : ℝ) (hε : 0 < ε)
    {θ : Space → ℝ} {η : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η) :
    (∫ x : Space, ‖physicalCorrection v x₀ T θ η ε (t, x)‖ ^ 2) =
      ε ^ 3 * ∫ z : Space, ‖profile v x₀ T θ η (ε, (ε ^ 2)⁻¹ * (t - T), z)‖ ^ 2 := by
  rw [physicalCorrection_eq_dilate hv x₀ T ε hε.ne' hθ hη]
  simpa only [Source.dilateField, slice, one_pow, one_mul] using
    energy_dilate_translate (fun z => profile v x₀ T θ η (ε, (ε ^ 2)⁻¹ * (t - T), z))
      1 ε hε x₀

/-- A uniform-in-time actual integral bound, equivalent to the squared
L∞_t L²_x estimate with rate ε³. -/
theorem physicalCorrection_uniform_energy {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ t : ℝ,
      (∫ x : Space, ‖physicalCorrection v x₀ T θ η ε (t, x)‖ ^ 2) ≤ C * ε ^ 3 := by
  obtain ⟨B, hB, hb⟩ := profile_uniform_global_derivative_bound hv x₀ T hθ hη hθc hηc 0
  refine ⟨volume.real (tsupport θ) * B ^ 2, by positivity, ?_⟩
  intro ε hε t
  rw [physicalCorrection_energy hv x₀ T ε t hε.1 hθ hη, mul_comm _ (ε ^ 3)]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hε.1.le 3)
  apply compact_energy_bound _ hθc B
  · intro z
    simpa only [norm_iteratedFDeriv_zero] using hb ε ⟨hε.1.le, hε.2⟩ ((ε ^ 2)⁻¹ * (t - T), z)
  · intro z hz
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact hz ((profile_support hv x₀ T hθ hη h).2.2)

/-- Exact spatial gradient energy scaling for each coordinate derivative. -/
theorem physicalCorrection_direction_energy {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T ε t : ℝ) (hε : 0 < ε)
    {θ : Space → ℝ} {η : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (e : Space) :
    (∫ x : Space, ‖spatialDerivative (physicalCorrection v x₀ T θ η ε) t x e‖ ^ 2) =
      ε * ∫ z : Space,
        ‖spaceDerivative (profile v x₀ T θ η) (ε, (ε ^ 2)⁻¹ * (t - T), z) e‖ ^ 2 := by
  rw [physicalCorrection_eq_dilate hv x₀ T ε hε.ne' hθ hη]
  simp_rw [Source.dilate_spatialDerivative, one_mul, smul_apply,
    spatialDerivative_slice (profile_smooth hv x₀ T hθ hη)]
  rw [energy_dilate_translate (fun z =>
    spaceDerivative (profile v x₀ T θ η) (ε, (ε ^ 2)⁻¹ * (t - T), z) e) _ ε hε]
  congr 1
  field_simp

theorem profile_direction_uniform_bound {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (e : Space) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Icc (0 : ℝ) 1, ∀ z : SpaceTime,
      ‖spaceDerivative (profile v x₀ T θ η) (ε, z) e‖ ≤ C := by
  have hc := ((spaceDerivative_smooth (profile_smooth hv x₀ T hθ hη)).clm_apply
    (contDiff_const (c := e))).continuous
  obtain ⟨B, hb⟩ := (isCompact_Icc.prod (hηc.prod hθc)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro ε hε z
  by_cases hz : z ∈ tsupport η ×ˢ tsupport θ
  · exact (hb (ε, z) ⟨hε, hz⟩).trans (le_max_left _ _)
  · have hn : (ε, z) ∉ tsupport (profile v x₀ T θ η) :=
      fun h => hz ((profile_support hv x₀ T hθ hη h).2)
    simp only [spaceDerivative, fderiv_of_notMem_tsupport ℝ hn,
      ContinuousLinearMap.zero_comp, zero_apply, norm_zero]
    exact le_max_right _ _

theorem physicalCorrection_uniform_direction_energy {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (e : Space) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ t : ℝ,
      (∫ x : Space, ‖spatialDerivative (physicalCorrection v x₀ T θ η ε) t x e‖ ^ 2) ≤ C * ε := by
  obtain ⟨B, hB, hb⟩ := profile_direction_uniform_bound hv x₀ T hθ hη hθc hηc e
  refine ⟨volume.real (tsupport θ) * B ^ 2, by positivity, ?_⟩
  intro ε hε t
  rw [physicalCorrection_direction_energy hv x₀ T ε t hε.1 hθ hη e, mul_comm _ ε]
  apply mul_le_mul_of_nonneg_left _ hε.1.le
  apply compact_energy_bound _ hθc B
  · intro z
    exact hb ε ⟨hε.1.le, hε.2⟩ _
  · intro z hz
    have hn : (ε, (ε ^ 2)⁻¹ * (t - T), z) ∉ tsupport (profile v x₀ T θ η) :=
      fun h => hz ((profile_support hv x₀ T hθ hη h).2.2)
    simp only [spaceDerivative, fderiv_of_notMem_tsupport ℝ hn,
      ContinuousLinearMap.zero_comp, zero_apply]

/-- The rescaled gradient energy density is genuinely integrable; the bounds
below do not rely on a nonintegrable Bochner integral defaulting to zero. -/
theorem profile_direction_energy_integrable {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T ε : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (e : Space) :
    Integrable (fun z : SpaceTime => ‖spaceDerivative (profile v x₀ T θ η) (ε, z) e‖ ^ 2) := by
  have hc : Continuous (fun z : SpaceTime =>
      ‖spaceDerivative (profile v x₀ T θ η) (ε, z) e‖ ^ 2) :=
    (((spaceDerivative_smooth (profile_smooth hv x₀ T hθ hη)).clm_apply contDiff_const).continuous.comp
      (continuous_const.prodMk continuous_id)).norm.pow 2
  apply hc.integrable_of_hasCompactSupport
  apply (hηc.prod hθc).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ ((isClosed_tsupport η).prod (isClosed_tsupport θ))
  intro z hz
  by_contra hn
  have hp : (ε, z) ∉ tsupport (profile v x₀ T θ η) :=
    fun h => hn ((profile_support hv x₀ T hθ hη h).2)
  apply hz
  simp only [spaceDerivative, fderiv_of_notMem_tsupport ℝ hp,
    ContinuousLinearMap.zero_comp, zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow]

theorem time_integral_bound (f : ℝ → ℝ) {K : Set ℝ} (hK : IsCompact K) (C : ℝ)
    (hf : ∀ t, 0 ≤ f t) (hb : ∀ t, f t ≤ C) (hs : ∀ t ∉ K, f t = 0) :
    (∫ t : ℝ, f t) ≤ volume.real K * C := by
  have hg : Integrable (K.indicator (fun _ : ℝ => C)) := by
    rw [integrable_indicator_iff hK.measurableSet]
    exact integrableOn_const hK.measure_ne_top
  calc
    _ ≤ ∫ t : ℝ, K.indicator (fun _ => C) t := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall hf) hg
      apply Filter.Eventually.of_forall
      intro t
      by_cases ht : t ∈ K
      · simpa [ht] using hb t
      · simp [ht, hs t ht]
    _ = _ := by rw [integral_indicator_const _ hK.measurableSet]; rfl

/-- The genuine spacetime gradient integral has the ε³ decay claimed for
the squared L²_t L²_x gradient norm. -/
theorem physicalCorrection_total_direction_energy {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (e : Space) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Ioc (0 : ℝ) 1,
      (∫ t : ℝ, ∫ x : Space,
        ‖spatialDerivative (physicalCorrection v x₀ T θ η ε) t x e‖ ^ 2) ≤ C * ε ^ 3 := by
  obtain ⟨B, hB, hb⟩ := profile_direction_uniform_bound hv x₀ T hθ hη hθc hηc e
  let C := volume.real (tsupport θ) * B ^ 2
  refine ⟨volume.real (tsupport η) * C, by dsimp [C]; positivity, ?_⟩
  intro ε hε
  let f : ℝ → ℝ := fun σ => ∫ z : Space,
    ‖spaceDerivative (profile v x₀ T θ η) (ε, σ, z) e‖ ^ 2
  have hf : ∀ σ, 0 ≤ f σ := fun σ => integral_nonneg (fun z => sq_nonneg _)
  have hbound : ∀ σ, f σ ≤ C := by
    intro σ
    apply compact_energy_bound _ hθc B
    · intro z
      exact hb ε ⟨hε.1.le, hε.2⟩ _
    · intro z hz
      have hn : (ε, σ, z) ∉ tsupport (profile v x₀ T θ η) :=
        fun h => hz ((profile_support hv x₀ T hθ hη h).2.2)
      simp only [spaceDerivative, fderiv_of_notMem_tsupport ℝ hn,
        ContinuousLinearMap.zero_comp, zero_apply]
  have hs : ∀ σ ∉ tsupport η, f σ = 0 := by
    intro σ hσ
    apply integral_eq_zero_of_ae
    apply Filter.Eventually.of_forall
    intro z
    have hn : (ε, σ, z) ∉ tsupport (profile v x₀ T θ η) :=
      fun h => hσ ((profile_support hv x₀ T hθ hη h).2.1)
    simp only [spaceDerivative, fderiv_of_notMem_tsupport ℝ hn,
      ContinuousLinearMap.zero_comp, zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, Pi.zero_apply]
  have htotal := time_integral_bound f hηc C hf hbound hs
  simp_rw [physicalCorrection_direction_energy hv x₀ T ε _ hε.1 hθ hη e]
  change (∫ t : ℝ, ε * f ((ε ^ 2)⁻¹ * (t - T))) ≤ _
  rw [integral_const_mul, integral_sub_right_eq_self (fun t : ℝ => f ((ε ^ 2)⁻¹ * t)) T]
  have hscale := Measure.integral_comp_smul_of_nonneg volume f ((ε ^ 2)⁻¹)
    (hR := (inv_nonneg.mpr (sq_nonneg ε)))
  simp only [Module.finrank_self, pow_one, inv_inv, smul_eq_mul] at hscale
  rw [hscale]
  calc
    ε * (ε ^ 2 * ∫ t : ℝ, f t) = ε ^ 3 * ∫ t : ℝ, f t := by ring
    _ ≤ ε ^ 3 * (volume.real (tsupport η) * C) :=
      mul_le_mul_of_nonneg_left htotal (pow_nonneg hε.1.le 3)
    _ = _ := by ring

end NSFormalization.Paper1.CorrectionEnergy
