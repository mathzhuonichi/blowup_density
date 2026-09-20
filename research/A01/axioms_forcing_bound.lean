import NSFormalization.Section4.A01.ForcingFamilyBound

noncomputable section
namespace NSFormalization.Section4.A01
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

-- The exact target is inhabited on zero data, for every competitor and limit.
example (q : ℕ) (hq : 6 ≤ q) :
    ForcingFamilyBound hq (by norm_num : (0 : ℝ) < 1)
      (SmoothL2Field.zeroField : SmoothL2Field Space)
      (fun _ : Icc (0 : ℝ) 1 => (SmoothL2Field.zeroField : SmoothL2Field Space))
      (fun _ => continuous_const) (E q) (A q) :=
  zero_forcing q hq (E q) (A q)

-- The spatial residual vanishes on genuine zero finite-order elements.
example (q : ℕ) (hq : 6 ≤ q) : cylinderCommutator hq 0 0 = 0 := by
  funext w
  simp [cylinderCommutator]

-- The spatial inequality itself is satisfied on zero data (not just its carrier equations).
example (q : ℕ) (hq : 6 ≤ q) :
    EulerFiniteMetricEnergy.familyNorm (cylinderCommutator hq 0 0) ≤
      A q * (16 * ‖restrictOperator 1 (Nat.succ_le_succ hq)
        (0 : SobolevSpace 1 (q+1))‖) * (0 : ℝ) := by
  simp [cylinderCommutator, EulerFiniteMetricEnergy.familyNorm,
    EulerFiniteMetricEnergy.familySquaredNorm]

-- A signed pairing bound alone cannot imply a family norm bound.
example : (1 : ℝ) * 0 ≤ 0 ∧ ¬ (|1| ≤ (0 : ℝ)) := by norm_num

#print axioms E
#print axioms A
#print axioms E_nonneg
#print axioms A_nonneg
#print axioms cylinderCommutator
#print axioms source_pressure_cancel
#print axioms CylinderCommutatorBound
#print axioms energyRawTime_ae
#print axioms energyForcingNorm_ae
#print axioms sourceTime_add_pressureTime_ae
#print axioms forcing_array_rearrange
#print axioms cylinderEnergyForcing_ae
#print axioms force_word_norm_le
#print axioms forcingFamilyBound_of_cylinder
#print axioms zero_value
#print axioms zero_sob
#print axioms zero_mild
#print axioms zero_forcing
end NSFormalization.Section4.A01
