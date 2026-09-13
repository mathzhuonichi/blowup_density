import NSFormalization.Paper3.AngularSobolevCoordinates
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

noncomputable section
namespace NSFormalization.Paper3
open MeasureTheory FourierTransform NavierStokes.ProblemStatement
open NSFormalization.Source
open scoped ENNReal SchwartzMap

def angularFrequencyScale : Space ≃L[ℝ] Space :=
  { LinearEquiv.smulOfNeZero ℝ Space frequencyUnit frequencyUnit_pos.ne' with
    continuous_toFun := continuous_const_smul _
    continuous_invFun := continuous_const_smul _ }

/-- Normalized dilation on Schwartz functions. -/
def schwartzAngularDilation : SchwartzMap Space ℂ →L[ℂ] SchwartzMap Space ℂ :=
  (frequencyUnit ^ (-3 / 2 : ℝ)) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ angularFrequencyScale.symm

/-- Its inverse is also the test map defining distributional dilation. -/
def schwartzAngularDilationInv : SchwartzMap Space ℂ →L[ℂ] SchwartzMap Space ℂ :=
  (frequencyUnit ^ (3 / 2 : ℝ)) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ angularFrequencyScale

@[simp] theorem schwartzAngularDilation_apply (φ : SchwartzMap Space ℂ) (ξ : Space) :
    schwartzAngularDilation φ ξ = frequencyUnit ^ (-3 / 2 : ℝ) • φ (frequencyUnit⁻¹ • ξ) := rfl

@[simp] theorem schwartzAngularDilationInv_apply (φ : SchwartzMap Space ℂ) (ξ : Space) :
    schwartzAngularDilationInv φ ξ = frequencyUnit ^ (3 / 2 : ℝ) • φ (frequencyUnit • ξ) := rfl

private theorem amplitude_inverse :
    frequencyUnit ^ (-3 / 2 : ℝ) * frequencyUnit ^ (3 / 2 : ℝ) = 1 := by
  rw [← Real.rpow_add frequencyUnit_pos]
  norm_num

private theorem amplitude_sq_jacobian :
    (frequencyUnit ^ (-3 / 2 : ℝ)) ^ 2 * frequencyUnit ^ 3 = 1 := by
  rw [← Real.rpow_mul_natCast frequencyUnit_pos.le, ← Real.rpow_natCast frequencyUnit 3,
    ← Real.rpow_add frequencyUnit_pos]
  norm_num

private theorem amplitude_jacobian :
    frequencyUnit ^ (-3 / 2 : ℝ) * frequencyUnit ^ 3 = frequencyUnit ^ (3 / 2 : ℝ) := by
  rw [← Real.rpow_natCast frequencyUnit 3, ← Real.rpow_add frequencyUnit_pos]
  norm_num

def schwartzAngularDilationEquiv : SchwartzMap Space ℂ ≃ₗ[ℂ] SchwartzMap Space ℂ :=
  { schwartzAngularDilation.toLinearMap with
    invFun := schwartzAngularDilationInv
    left_inv := by
      intro φ
      ext ξ
      change schwartzAngularDilationInv (schwartzAngularDilation φ) ξ = φ ξ
      simp only [schwartzAngularDilationInv_apply, schwartzAngularDilation_apply,
        inv_smul_smul₀ frequencyUnit_pos.ne', smul_smul]
      rw [mul_comm, amplitude_inverse, one_smul]
    right_inv := by
      intro φ
      ext ξ
      change schwartzAngularDilation (schwartzAngularDilationInv φ) ξ = φ ξ
      simp only [schwartzAngularDilationInv_apply, schwartzAngularDilation_apply,
        smul_inv_smul₀ frequencyUnit_pos.ne', smul_smul]
      rw [amplitude_inverse, one_smul] }

/-- The normalized amplitude cancels the genuine Haar-volume Jacobian. -/
theorem schwartzAngularDilation_norm_toLp (φ : SchwartzMap Space ℂ) :
    ‖(schwartzAngularDilation φ).toLp 2 volume‖ = ‖φ.toLp 2 volume‖ := by
  rw [SchwartzMap.norm_toLp' (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
    SchwartzMap.norm_toLp' (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two]
  apply congrArg (fun r : ℝ => r ^ (1 / 2 : ℝ))
  simp_rw [schwartzAngularDilation_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [integral_const_mul, Measure.integral_comp_inv_smul volume (fun ξ : Space => ‖φ ξ‖ ^ 2)]
  rw [show Module.finrank ℝ Space = 3 by simp [Space]]
  rw [abs_of_pos (pow_pos frequencyUnit_pos 3), smul_eq_mul, ← mul_assoc,
    amplitude_sq_jacobian, one_mul]

/-- The actual unitary normalized frequency dilation on all L2 data. -/
def angularFrequencyDilation : Lp ℂ 2 (volume : Measure Space) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure Space) :=
  schwartzAngularDilationEquiv.extendOfIsometry
    (SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap (SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap
    (SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top)
    (SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top)
    schwartzAngularDilation_norm_toLp

@[simp] theorem angularFrequencyDilation_toLp (φ : SchwartzMap Space ℂ) :
    angularFrequencyDilation (φ.toLp 2 volume) = (schwartzAngularDilation φ).toLp 2 volume := by
  exact LinearEquiv.extendOfIsometry_eq schwartzAngularDilationEquiv
    (SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap (SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap
    (SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top)
    (SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top) schwartzAngularDilation_norm_toLp φ

/-- Normalized distribution dilation, defined by its actual test action. -/
def angularDistributionDilation : 𝓢'(Space, ℂ) →L[ℂ] 𝓢'(Space, ℂ) :=
  PointwiseConvergenceCLM.precomp ℂ schwartzAngularDilationInv

theorem angularDistributionDilation_apply (U : 𝓢'(Space, ℂ)) (ψ : SchwartzMap Space ℂ) :
    angularDistributionDilation U ψ = frequencyUnit ^ (3 / 2 : ℝ) •
      U (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ angularFrequencyScale ψ) := by
  change U (frequencyUnit ^ (3 / 2 : ℝ) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ angularFrequencyScale ψ) = _
  exact U.map_smul_of_tower _ _

/-- Change of variables with the true c³ Jacobian identifies the Schwartz
function dilation with the distribution test action. -/
theorem angularDistributionDilation_schwartz (φ : SchwartzMap Space ℂ) :
    angularDistributionDilation (φ : 𝓢'(Space, ℂ)) =
      (schwartzAngularDilation φ : 𝓢'(Space, ℂ)) := by
  ext ψ
  change (∫ x : Space, schwartzAngularDilationInv ψ x • φ x) =
    ∫ x : Space, ψ x • schwartzAngularDilation φ x
  simp_rw [schwartzAngularDilationInv_apply, schwartzAngularDilation_apply,
    smul_assoc, smul_comm (ψ _) (frequencyUnit ^ (-3 / 2 : ℝ))]
  rw [integral_smul, integral_smul]
  have hscale : (∫ x : Space, ψ x • φ (frequencyUnit⁻¹ • x)) =
      frequencyUnit ^ 3 • ∫ x : Space, ψ (frequencyUnit • x) • φ x := by
    have H := Measure.integral_comp_inv_smul volume
      (fun x : Space => ψ (frequencyUnit • x) • φ x) frequencyUnit
    simpa only [smul_inv_smul₀ frequencyUnit_pos.ne',
      show Module.finrank ℝ Space = 3 by simp [Space], abs_of_pos (pow_pos frequencyUnit_pos 3)] using H
  rw [hscale, smul_smul, amplitude_jacobian]

/-- The normalized unitary L2 dilation has exactly the declared distribution
action, including arbitrary non-L1 data. -/
theorem angularFrequencyDilation_toDistribution (k : Lp ℂ 2 (volume : Measure Space)) :
    (angularFrequencyDilation k : 𝓢'(Space, ℂ)) =
      angularDistributionDilation (k : 𝓢'(Space, ℂ)) := by
  refine (SchwartzMap.denseRange_toLpCLM (E := Space) (F := ℂ) (p := 2)
    (μ := volume) ENNReal.ofNat_ne_top).induction_on k
    (isClosed_eq
      ((Lp.toTemperedDistributionCLM ℂ volume 2).continuous.comp angularFrequencyDilation.continuous)
      (angularDistributionDilation.continuous.comp (Lp.toTemperedDistributionCLM ℂ volume 2).continuous)) ?_
  intro φ
  change (angularFrequencyDilation (φ.toLp 2 volume) : 𝓢'(Space, ℂ)) =
    angularDistributionDilation (φ.toLp 2 volume : 𝓢'(Space, ℂ))
  rw [angularFrequencyDilation_toLp, Lp.toTemperedDistribution_toLp_eq,
    Lp.toTemperedDistribution_toLp_eq]
  exact (angularDistributionDilation_schwartz φ).symm

/-- Dilation intertwines the two genuine Bessel multiplier actions. -/
theorem angularDistributionDilation_weight_cancel (s : ℝ) (U : 𝓢'(Space, ℂ)) :
    sobolevWeightMultiplier s (angularDistributionDilation
      (TemperedDistribution.smulLeftCLM ℂ
        (fun ξ => sobolevBesselWeight (-s) (frequencyUnit • ξ)) U)) =
      angularDistributionDilation U := by
  have hg : (fun ξ => sobolevBesselWeight (-s) (frequencyUnit • ξ)).HasTemperateGrowth :=
    (sobolevBesselWeight_temperate (-s)).comp
      ((frequencyUnit • ContinuousLinearMap.id ℝ Space).hasTemperateGrowth)
  ext ψ
  change U (SchwartzMap.smulLeftCLM ℂ
      (fun ξ => sobolevBesselWeight (-s) (frequencyUnit • ξ))
      (schwartzAngularDilationInv (SchwartzMap.smulLeftCLM ℂ (sobolevBesselWeight s) ψ))) =
    U (schwartzAngularDilationInv ψ)
  apply congrArg U
  ext ξ
  rw [SchwartzMap.smulLeftCLM_apply_apply hg, schwartzAngularDilationInv_apply,
    SchwartzMap.smulLeftCLM_apply_apply (sobolevBesselWeight_temperate s),
    schwartzAngularDilationInv_apply]
  simp only [smul_eq_mul, Complex.real_smul]
  have hcan : sobolevBesselWeight (-s) (frequencyUnit • ξ) *
      sobolevBesselWeight s (frequencyUnit • ξ) = 1 := by
    have H := congrFun (sobolevBesselWeight_mul (-s) s) (frequencyUnit • ξ)
    simpa [sobolevBesselWeight] using H
  calc
    _ = ((frequencyUnit ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
        (sobolevBesselWeight (-s) (frequencyUnit • ξ) * sobolevBesselWeight s (frequencyUnit • ξ)) *
        ψ (frequencyUnit • ξ) := by ring
    _ = _ := by rw [hcan]; ring

/-- The normalized angular Fourier transform on actual tempered distributions. -/
def angularFourierDistribution : 𝓢'(Space, ℂ) →L[ℂ] 𝓢'(Space, ℂ) :=
  angularDistributionDilation.comp (fourierCLM ℂ 𝓢'(Space, ℂ))

/-- Realization from actual normalized angular-frequency L2 data. -/
def angularRealization (s : ℝ) : Lp ℂ 2 (volume : Measure Space) →L[ℂ] 𝓢'(Space, ℂ) :=
  (angularCoordinateRealization s).comp
    angularFrequencyDilation.symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- The complete angular transform of coordinate data has exactly the
weighted unitary dilation as its Fourier representative. -/
theorem weightedAngularFourier_coordinate (s : ℝ) (k : Lp ℂ 2 (volume : Measure Space)) :
    sobolevWeightMultiplier s (angularFourierDistribution (angularCoordinateRealization s k)) =
      (angularFrequencyDilation k : 𝓢'(Space, ℂ)) := by
  change sobolevWeightMultiplier s (angularDistributionDilation (𝓕 (angularCoordinateRealization s k))) = _
  rw [fourier_angularCoordinateRealization, angularDistributionDilation_weight_cancel,
    angularFrequencyDilation_toDistribution]

/-- Exact weighted angular reconstruction for arbitrary complete L2 data,
including non-L1 backgrounds. -/
theorem weightedAngularFourier_realization (s : ℝ) (l : Lp ℂ 2 (volume : Measure Space)) :
    sobolevWeightMultiplier s (angularFourierDistribution (angularRealization s l)) =
      (l : 𝓢'(Space, ℂ)) := by
  change sobolevWeightMultiplier s (angularFourierDistribution
    (angularCoordinateRealization s (angularFrequencyDilation.symm l))) = _
  rw [weightedAngularFourier_coordinate, LinearIsometryEquiv.apply_symm_apply]

theorem angularRealization_preserves_coordinate (s : ℝ) (k : Lp ℂ 2 (volume : Measure Space)) :
    angularRealization s (angularFrequencyDilation k) = angularCoordinateRealization s k := by
  change angularCoordinateRealization s (angularFrequencyDilation.symm (angularFrequencyDilation k)) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

theorem angularRealization_injective (s : ℝ) : Function.Injective (angularRealization s) :=
  (angularCoordinateRealization_injective s).comp angularFrequencyDilation.symm.injective

/-- On the Schwartz core, the normalized transform is the manuscript's
actual angular Fourier function. -/
theorem schwartzAngularDilation_fourier_apply (φ : SchwartzMap Space ℂ) (ξ : Space) :
    schwartzAngularDilation (𝓕 φ) ξ = angularFourier (φ : Space → ℂ) ξ := rfl

theorem angularFourierDistribution_schwartz (φ : SchwartzMap Space ℂ) :
    angularFourierDistribution (φ : 𝓢'(Space, ℂ)) =
      (schwartzAngularDilation (𝓕 φ) : 𝓢'(Space, ℂ)) := by
  change angularDistributionDilation (𝓕 (φ : 𝓢'(Space, ℂ))) = _
  rw [TemperedDistribution.fourier_toTemperedDistributionCLM_eq,
    angularDistributionDilation_schwartz]

theorem angularFourierDistribution_schwartz_apply (φ ψ : SchwartzMap Space ℂ) :
    angularFourierDistribution (φ : 𝓢'(Space, ℂ)) ψ =
      ∫ ξ : Space, ψ ξ • angularFourier (φ : Space → ℂ) ξ := by
  rw [angularFourierDistribution_schwartz, SchwartzMap.coe_apply]
  simp only [schwartzAngularDilation_fourier_apply]

/-- Actual angular-frequency weighted data for a Schwartz physical field. -/
def angularDatum (s : ℝ) (φ : SchwartzMap Space ℂ) : Lp ℂ 2 (volume : Measure Space) :=
  angularFrequencyDilation (angularCoordinateDatum s φ)

theorem norm_angularDatum (s : ℝ) (φ : SchwartzMap Space ℂ) :
    ‖angularDatum s φ‖ = angularSobolevNorm s (φ : Space → ℂ) := by
  rw [angularDatum, angularFrequencyDilation.norm_map, norm_angularCoordinateDatum]

@[simp] theorem angularRealization_datum (s : ℝ) (φ : SchwartzMap Space ℂ) :
    angularRealization s (angularDatum s φ) = (φ : 𝓢'(Space, ℂ)) := by
  rw [angularDatum, angularRealization_preserves_coordinate, angularCoordinateRealization_datum]

end NSFormalization.Paper3
