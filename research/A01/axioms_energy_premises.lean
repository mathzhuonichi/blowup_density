import NSFormalization.Section4.A01.MildEnergyPremises

set_option format.width 240

noncomputable section
namespace NSFormalization.Section4.A01
#print axioms energyRawPath
#print axioms energyPressurePath
#print axioms energyPressurePath_gradient
#print axioms energyRawTime
#print axioms energyPressureTime
#print axioms energyRawTime_restriction
#print axioms energyPressureTime_restriction
#print axioms energy_velocity_divergenceFree
#print axioms energy_maximal_limit
#print axioms energyIdentity
#print axioms energyRootPath
#print axioms energyRootPath_apply
#print axioms energyForcingNorm
#print axioms energy_estimate_of_representatives
#print axioms energy_force_restriction
#print axioms cylinderEnergyForcing
#print axioms mild_energy_estimate_of_cylinder
#print axioms energyGradientNorm
#print axioms ForcingFamilyBound
#print axioms EnvelopeConversion
#print axioms finiteMildEnergy_of_estimate

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

/-- The sole analytic premise is discharged, for every zero-data competitor
and every finite order, rather than assumed in the example. -/
private theorem zero_energy (q : ℕ) (hq : 6 ≤ q) (E A : ℝ) :
    FiniteMildEnergy hq (by norm_num : (0 : ℝ) < 1)
      (SmoothL2Field.zeroField : SmoothL2Field Space)
      (by intro x; simp [EulerSmoothLimit.divergence, SmoothL2Field.zeroField])
      (fun _ : Icc (0 : ℝ) 1 => (SmoothL2Field.zeroField : SmoothL2Field Space))
      (fun _ => continuous_const) E A := by
  intro T hT hTS u hu
  have he := quadratic_mild_unique_window (by norm_num : (0 : ℝ) < 1) hT hTS _ _ u 0
    hu (zero_mild q hq hT hTS)
  subst u
  refine ⟨0, fun _ => 0, fun _ => 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro t; simp
  · intro t; simp
  · simp [zero_sob]
  · intro t _
    change HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 t
    exact hasDerivAt_const t 0
  · intro t _
    simp [extendPath]


-- All maximal limits and all competitors are covered, not merely a chosen zero path.
private theorem zero_forcing (q : ℕ) (hq : 6 ≤ q) (E A : ℝ) :
    ForcingFamilyBound hq (by norm_num : (0 : ℝ) < 1)
      (SmoothL2Field.zeroField : SmoothL2Field Space)
      (fun _ : Icc (0 : ℝ) 1 => (SmoothL2Field.zeroField : SmoothL2Field Space))
      (fun _ => continuous_const) E A := by
  intro T hT hTS u hu U _
  have he := quadratic_mild_unique_window (by norm_num : (0 : ℝ) < 1) hT hTS _ _ u 0
    hu (zero_mild q hq hT hTS)
  subst u
  apply Filter.Eventually.of_forall
  intro r
  simp [extendPath, energyRootPath_apply, euclideanWordNorm_eq]

private theorem zero_envelope (q : ℕ) (hq : 6 ≤ q) (E A : ℝ) :
    EnvelopeConversion hq (by norm_num : (0 : ℝ) < 1)
      (SmoothL2Field.zeroField : SmoothL2Field Space)
      (fun _ : Icc (0 : ℝ) 1 => (SmoothL2Field.zeroField : SmoothL2Field Space))
      (fun _ => continuous_const) E A := by
  intro T hT hTS u hu U _ _ _
  exact zero_energy q hq E A T hT hTS u hu

-- Apply this lane's new estimate and both discharged inputs on zero data.
example (q : ℕ) (hq : 6 ≤ q) :
    FiniteMildEnergy hq (by norm_num : (0 : ℝ) < 1)
      (SmoothL2Field.zeroField : SmoothL2Field Space)
      (by intro x; simp [EulerSmoothLimit.divergence, SmoothL2Field.zeroField])
      (fun _ : Icc (0 : ℝ) 1 => (SmoothL2Field.zeroField : SmoothL2Field Space))
      (fun _ => continuous_const) 1 0 :=
  finiteMildEnergy_of_estimate hq (by norm_num) _ _ _ _ 1 0
    (zero_forcing q hq 1 0) (zero_envelope q hq 1 0)

-- A nonzero dissipation cannot be recovered from a constant root and Z=0 alone.
example : ¬ ((1/2 : ℝ) * 0 + 1 * 1^2 ≤ 0) := by norm_num

#print axioms zero_value
#print axioms zero_sob
#print axioms zero_mild
#print axioms zero_energy
#print axioms zero_forcing
#print axioms zero_envelope
end NSFormalization.Section4.A01
