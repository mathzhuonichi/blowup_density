import NSFormalization.Section4.A01.RootComparison

set_option format.width 240

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

private theorem zero_signed_limit (q : ℕ) (hq : 6 ≤ q) (E A : ℝ) :
    CylinderSignedRootLimit hq (by norm_num : (0 : ℝ) < 1)
      (SmoothL2Field.zeroField : SmoothL2Field Space)
      (by intro x; simp [EulerSmoothLimit.divergence, SmoothL2Field.zeroField])
      (fun _ : Icc (0 : ℝ) 1 => (SmoothL2Field.zeroField : SmoothL2Field Space))
      (fun _ => continuous_const) E A := by
  intro T hT hTS u hu U _ _ t _
  have he := quadratic_mild_unique_window (by norm_num : (0 : ℝ) < 1) hT hTS _ _ u 0
    hu (zero_mild q hq hT hTS)
  subst u
  have hf : sobolevPath
      (fun _ : Icc (0 : ℝ) 1 => (SmoothL2Field.zeroField : SmoothL2Field Space))
      (fun _ => continuous_const) (q+1) = 0 := by
    apply ContinuousMap.ext
    intro t
    exact zero_sob (q+1)
  simp [extendPath, energyRootPath_apply, euclideanWordNorm_eq, hf]

-- Both hypotheses are constructed for every zero-data competitor and maximal limit.
example (q : ℕ) (hq : 6 ≤ q) :
    FiniteMildEnergy hq (by norm_num : (0 : ℝ) < 1)
      (SmoothL2Field.zeroField : SmoothL2Field Space)
      (by intro x; simp [EulerSmoothLimit.divergence, SmoothL2Field.zeroField])
      (fun _ : Icc (0 : ℝ) 1 => (SmoothL2Field.zeroField : SmoothL2Field Space))
      (fun _ => continuous_const) (mildNormConstant q) 1 :=
  finiteMildEnergy_of_forcingBound hq (by norm_num) _ _ _ _ le_rfl
    (zero_signed_limit q hq _ _) (zero_forcing q hq _ _)

-- Zero root, zero horizon, and a nonstationary zero-initial-root solution.
example : (0 : ℝ) ≤ energyComparison (fun _ => 0) 0 0 0 := by
  exact scalar_integral_comparison (T := 0) le_rfl continuous_const continuous_const
    (by simp) (by simp) 0 ⟨le_rfl, le_rfl⟩

example (T : ℝ) (hT : 0 ≤ T) (t : ℝ) (ht : t ∈ Icc 0 T) :
    t = energyComparison (fun _ => 0) 1 0 t :=
  energyComparison_unique_on_Icc hT continuous_const continuous_id.continuousOn rfl
    (fun s _ => by simpa using hasDerivAt_id s) t ht

example (t : ℝ) : (0 : ℝ) ≤ energyComparison (fun _ => 0) 0 0 t := by
  apply regularized_root_comparison_limit (fun _ => 0) le_rfl le_rfl
  intro ε _
  simp [energyComparison]

-- Initial normalization cannot be inferred from a vanishing forcing product.
example : (1 : ℝ)*0 ≤ 0 ∧ ¬ ((1 : ℝ) ≤ energyComparison (fun _ => 0) 0 0 0) := by
  simp [energyComparison_zero]

-- A dissipation-free constant-root estimate cannot retain prescribed g=1.
example : ¬ ((1/2 : ℝ)*0+1*1^2 ≤ 0) := by norm_num

#print axioms scalar_differential_comparison
#print axioms scalar_integral_comparison
#print axioms energyComparison_unique_on_Icc
#print axioms regularized_root_comparison_limit
#print axioms positive_root_absorption
#print axioms CylinderSignedRootLimit
#print axioms cylinderRootComparison_of_forcingBound
#print axioms finiteMildEnergy_of_forcingBound
#print axioms zero_value
#print axioms zero_sob
#print axioms zero_mild
#print axioms zero_forcing
#print axioms zero_signed_limit
end NSFormalization.Section4.A01
