import NSFormalization.Section4.A01.AprioriFamily

noncomputable section
namespace NSFormalization.Section4.A01
#print axioms quadratic_mild_prefix
#print axioms quadratic_mild_unique_window
#print axioms base_identification
#print axioms hasAprioriBound_base
#print axioms lower_identification
#print axioms exists_base_apriori
#print axioms h2_cap_transfer
#print axioms MildGronwall
#print axioms aprioriRadius
#print axioms hb_of_base
#print axioms hb_of_base_inv


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

-- No bound or PDE premise is assumed: every zero-data competitor is identified with zero.
example : ∀ q (hq : 6 ≤ q), HasAprioriBound hq (by norm_num : (0 : ℝ) < 1)
    (SmoothL2Field.zeroField : SmoothL2Field Space)
    (fun _ : Icc (0 : ℝ) 1 => (SmoothL2Field.zeroField : SmoothL2Field Space))
    (fun _ => continuous_const)
    (aprioriRadius (S := 1) SmoothL2Field.zeroField (fun _ => SmoothL2Field.zeroField)
      (fun _ => continuous_const) 0 (fun _ => 1) (fun _ => 1) q) := by
  apply hb_of_base (by norm_num) (by norm_num) _ _ _ 0 (by simp)
    (zero_mild 6 le_rfl (by norm_num) le_rfl) (fun _ => 1) (fun _ => 1)
    (fun _ => by norm_num) (fun _ => by norm_num)
  intro q hq T hT hTS u hu
  have he := quadratic_mild_unique_window (by norm_num : (0 : ℝ) < 1) hT hTS _ _ u 0
    hu (zero_mild q hq hT hTS)
  subst u
  refine ⟨0, ?_, ?_, ?_⟩
  · intro t; simp
  · simp only [ContinuousMap.zero_apply, zero_sob, norm_zero, mul_zero, le_refl]
  · intro t
    have hf : sobolevPath (fun _ : Icc (0 : ℝ) 1 =>
        (SmoothL2Field.zeroField : SmoothL2Field Space)) (fun _ => continuous_const) (q+1) = 0 := by
      apply ContinuousMap.ext
      intro t
      exact zero_sob (q+1)
    simp only [ContinuousMap.zero_apply, extendPath, map_zero, norm_zero, zero_pow,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_zero, add_zero, hf,
      intervalIntegral.integral_zero, le_refl]

#print axioms zero_value
#print axioms zero_sob
#print axioms zero_mild
end NSFormalization.Section4.A01
