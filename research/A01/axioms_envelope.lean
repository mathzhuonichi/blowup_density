import NSFormalization.Section4.A01.MildEnergyEnvelope

set_option format.width 240
noncomputable section
namespace NSFormalization.Section4.A01
#print axioms identity_jetLaplacian_pairing
#print axioms full_word_energy_hasDerivAt
#print axioms regularized_full_energy_hasDerivAt
#print axioms energyComparison
#print axioms energyComparison_hasDerivAt
#print axioms energyComparison_zero
#print axioms energyComparison_unique
#print axioms energyComparison_nonneg
#print axioms energyComparison_balance
#print axioms squared_comparison_envelope
#print axioms comparison_envelope
#print axioms cylinderEnvelopeDriver
#print axioms cylinderEnvelopeDriver_continuous
#print axioms CylinderRootComparison
#print axioms finiteMildEnergy_of_rootComparison
#print axioms envelopeConversion_of_rootComparison
#print axioms mildGronwall_of_rootComparison
#print axioms hb_of_base_of_rootComparison

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift
open EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
open EulerSmoothFieldSobolevTime EulerQuadraticSource EulerSobolevHeat EulerVolterraConvolution
open NSFormalization.Source.ForcedCylinderLocal
open scoped Topology ContDiff
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

private theorem zero_value : (SmoothL2Field.zeroField : SmoothL2Field Space).toLp = 0 := by
  apply Lp.ext
  filter_upwards [(SmoothL2Field.zeroField : SmoothL2Field Space).toLp_ae,
    Lp.coeFn_zero Space 2 volume] with x hx hz
  exact hx.trans hz.symm

private theorem zero_sob (q : ℕ) : ordinarySobolev q
    (SmoothL2Field.zeroField : SmoothL2Field Space).toLp
    (SmoothL2Field.zeroField : SmoothL2Field Space).translation_contDiff = 0 := by
  apply value_injective 1
  simp only [ordinarySobolev_value, zero_value, map_zero]
  rfl

private theorem zero_mild (q : ℕ) (hq : 6 ≤ q) {T : ℝ} (hT : 0 ≤ T)
    (hTS : T ≤ 1) : ∀ t,
    (0 : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))) t =
      quadraticDuhamel 1 1 (by norm_num) hT hTS
        (coefficients 1 hq (sobolevPath
          (fun _ : Icc (0 : ℝ) 1 => (SmoothL2Field.zeroField : SmoothL2Field Space))
          (fun _ => continuous_const) q))
        (ordinarySobolev (q+1) (SmoothL2Field.zeroField : SmoothL2Field Space).toLp
          (SmoothL2Field.zeroField : SmoothL2Field Space).translation_contDiff) 0 t := by
  intro t
  simp only [quadraticDuhamel, source_eq, ContinuousMap.zero_apply, zero_sob,
    map_zero, sobolevPath, ContinuousMap.coe_mk, sub_zero, intervalIntegral.integral_zero,
    add_zero]

private theorem zero_comparison (q : ℕ) (hq : 6 ≤ q) {E A : ℝ} (hE : 0 ≤ E) :
    CylinderRootComparison hq (by norm_num : (0 : ℝ) < 1)
      (SmoothL2Field.zeroField : SmoothL2Field Space)
      (fun _ : Icc (0 : ℝ) 1 => (SmoothL2Field.zeroField : SmoothL2Field Space))
      (fun _ => continuous_const) E A := by
  intro T hT hTS u hu t
  have he := quadratic_mild_unique_window (by norm_num : (0 : ℝ) < 1) hT hTS _ _ u 0
    hu (zero_mild q hq hT hTS)
  subst u
  have hz : energyRootPath (0 : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))) t = 0 := by
    simp [energyRootPath_apply, euclideanWordNorm_eq]
  rw [hz]
  exact energyComparison_nonneg _ (mul_nonneg hE (norm_nonneg _))
    (mul_nonneg hE (norm_nonneg _)) t.property.1

-- The residual is proved for all zero-data competitors, not assumed.
example (q : ℕ) (hq : 6 ≤ q) :
    FiniteMildEnergy hq (by norm_num : (0 : ℝ) < 1)
      (SmoothL2Field.zeroField : SmoothL2Field Space)
      (by intro x; simp [EulerSmoothLimit.divergence, SmoothL2Field.zeroField])
      (fun _ : Icc (0 : ℝ) 1 => (SmoothL2Field.zeroField : SmoothL2Field Space))
      (fun _ => continuous_const) (mildNormConstant q) 1 :=
  finiteMildEnergy_of_rootComparison hq (by norm_num) _ _ _ _
    (mildNormConstant_nonneg q) (zero_comparison q hq (mildNormConstant_nonneg q))

example (q : ℕ) (hq : 6 ≤ q) :
    EnvelopeConversion hq (by norm_num : (0 : ℝ) < 1)
      (SmoothL2Field.zeroField : SmoothL2Field Space)
      (fun _ : Icc (0 : ℝ) 1 => (SmoothL2Field.zeroField : SmoothL2Field Space))
      (fun _ => continuous_const) (mildNormConstant q) 1 :=
  envelopeConversion_of_rootComparison hq (by norm_num) _
    (by intro x; simp [EulerSmoothLimit.divergence, SmoothL2Field.zeroField]) _ _
    (mildNormConstant_nonneg q) (zero_comparison q hq (mildNormConstant_nonneg q))

-- A nonstationary scalar witness; the comparison does not require positive initial energy.
example (t : ℝ) : energyComparison (fun _ => 0) 1 1 t = 1 + t := by
  simp [energyComparison]

example (t : ℝ) : energyComparison (fun _ => 0) 1 0 t = t := by
  simp [energyComparison]

-- Dropping viscosity cannot later recover a prescribed positive gradient.
-- This does not disprove EnvelopeConversion, where the gradient is existential.
example : ¬ ((1/2 : ℝ) * 0 + 1 * 1^2 ≤ 0) := by norm_num

-- A bound on a signed scalar pairing cannot bound the forcing norm:
-- e=1, forcing=-2 has pairing -2 <= 0 but root*norm(forcing)=2 > 0.
example : (1 : ℝ) * (-2) ≤ 0 ∧ ¬ ((1 : ℝ) * |-2| ≤ 0) := by norm_num

#print axioms zero_value
#print axioms zero_sob
#print axioms zero_mild
#print axioms zero_comparison
end NSFormalization.Section4.A01
