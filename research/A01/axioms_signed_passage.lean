import NSFormalization.Section4.A01.SignedPassage

set_option format.width 240

noncomputable section
namespace NSFormalization.Section4.A01
open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift
open EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
open EulerSmoothFieldSobolevTime EulerQuadraticSource EulerSobolevHeat EulerVolterraConvolution
open NSFormalization.Source.ForcedCylinderLocal
open EulerTimeLp EulerRegularizedTopBlocks
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

-- Positive-horizon non-vacuity: the forcing bound covers every competitor.
-- The general passage itself is proved in the imported module.
example (q : ℕ) (hq : 6 ≤ q) :
    FiniteMildEnergy hq (by norm_num : (0 : ℝ) < 1)
      (SmoothL2Field.zeroField : SmoothL2Field Space)
      (by intro x; simp [EulerSmoothLimit.divergence, SmoothL2Field.zeroField])
      (fun _ : Icc (0 : ℝ) 1 => (SmoothL2Field.zeroField : SmoothL2Field Space))
      (fun _ => continuous_const) (max 1 (mildNormConstant q)) 0 :=
  finiteMildEnergy_of_forcingBound'' hq (by norm_num) _ _ _ _ (le_max_right _ _)
    (zero_forcing q hq _ _)

-- At zero horizon the signed scalar theorem still returns integrability.
example : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 0 := intervalIntegrable_const

-- Nonzero dissipating scalar path, ν=ε=1, on a positive horizon.
example : ∀ t ∈ Icc (0 : ℝ) 1,
    Real.sqrt (Real.exp (-2*t)+1) ≤ Real.sqrt (Real.exp (-2*0)+1) +
      ∫ s in (0 : ℝ)..t, -Real.exp (-2*s)/Real.sqrt (Real.exp (-2*s)+1) := by
  have hd (s : ℝ) : HasDerivAt (fun s : ℝ => Real.exp (-2*s))
      (2*0-2*1*Real.exp (-2*s)) s := by
    convert ((hasDerivAt_id s).const_mul (-2)).exp using 1 <;> first | rfl | (dsimp; ring)
  have H := signed_scalar_integral (ν := 1) (ε := 1) (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num) (fun s => Real.exp (-2*s)) (fun _ => 0) (fun s => Real.exp (-2*s))
    (fun _ => 0) (by fun_prop) continuous_const (by fun_prop) continuous_const
    (fun s => (Real.exp_pos _).le) (fun s _ => hd s) (fun s _ => by simp)
  intro t ht
  simpa using (H t ht).2

-- A doubled dissipative coefficient would be a strictly stronger derivative claim.
example : ¬ (-(1 : ℝ)/Real.sqrt 2 ≤ -2/Real.sqrt 2) := by
  rw [div_le_div_iff_of_pos_right (by positivity : 0 < Real.sqrt 2)]
  norm_num

#print axioms signedWordPath
#print axioms signedApproximationRoot
#print axioms signedApproximationDissipation
#print axioms signedApproximationForcing
#print axioms signedApproximationRoot_apply
#print axioms signedApproximationRoot_tendsto
#print axioms signed_transport_zero
#print axioms signed_source_pairing_le
#print axioms signed_scalar_integral
#print axioms regularized_signed_energy_inequality
#print axioms signed_subintervalWeight_tendsto
#print axioms signed_forcing_integral_tendsto
#print axioms signedRootCoefficient
#print axioms signedRootCoefficient_tendsto
#print axioms signedApproximationForcing_tendsto
#print axioms signed_scalar_multiplier_tendsto
#print axioms signed_weighted_square_limit
#print axioms signedGradientOperator
#print axioms signedGradientOperator_apply
#print axioms signedGradientOperator_norm_sq
#print axioms signedApproximationDissipation_eq
#print axioms signedGradientOperator_ae
#print axioms signedInverseRoot
#print axioms maximal_weighted_dissipation_limit
#print axioms cylinderSignedEnergyPassage
#print axioms cylinderSignedRootLimit_of_forcingBound'
#print axioms finiteMildEnergy_of_forcingBound''
#print axioms zero_value
#print axioms zero_sob
#print axioms zero_mild
#print axioms zero_forcing
end NSFormalization.Section4.A01
