import NSFormalization.Section4.A01.MildGronwall

noncomputable section
namespace NSFormalization.Section4.A01
#print axioms mildNormConstant
#print axioms mildNormConstant_nonneg
#print axioms euclideanWordNorm
#print axioms euclideanWordNorm_eq
#print axioms euclideanWordNorm_bounds
#print axioms continuous_euclideanWordNorm
#print axioms euclidean_full_word_limit
#print axioms quadratic_regularized_word
#print axioms mild_energy_absorption
#print axioms outer_tame_low
#print axioms inner_mild_energy
#print axioms FiniteMildEnergy
#print axioms mildGronwall
#print axioms hb_of_base'
#print axioms hb_of_base_inv'

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

-- Explicit constants on zero data: E(q)=1, A(q)=0, C(q)=0, radius=0.
example : ∀ q (hq : 6 ≤ q), HasAprioriBound hq (by norm_num : (0 : ℝ) < 1)
    (SmoothL2Field.zeroField : SmoothL2Field Space)
    (fun _ : Icc (0 : ℝ) 1 => (SmoothL2Field.zeroField : SmoothL2Field Space))
    (fun _ => continuous_const)
    (aprioriRadius (S := 1) SmoothL2Field.zeroField (fun _ => SmoothL2Field.zeroField)
      (fun _ => continuous_const) 0 (fun _ => 1) (fun _ => 0^2/(4*1)) q) := by
  exact hb_of_base' (by norm_num) (by norm_num) _
    (by intro x; simp [EulerSmoothLimit.divergence, SmoothL2Field.zeroField]) _ _ 0 (by simp)
    (zero_mild 6 le_rfl (by norm_num) le_rfl) (fun _ => 1) (fun _ => 0)
    (fun _ => by norm_num) (fun q hq => zero_energy q hq 1 0)

-- Dropping finiteness from a toReal transport is actually false.
example : ¬ (∀ a b : ENNReal, a ≤ b → a.toReal ≤ b.toReal) := by
  intro h
  have hh := h 1 ⊤ le_top
  norm_num at hh

-- A nonstationary, nonzero scalar instance of the unabsorbed inequality.
-- Thus differentiability in the residual does not demand stationary envelopes.
example (t : ℝ) (ht : 0 ≤ t) :
    (1/2 : ℝ) * (2*(1+t)) + 1*0^2 ≤
      0*(16*0)*Real.sqrt ((1+t)^2)*0 + 1*Real.sqrt ((1+t)^2) := by
  rw [Real.sqrt_sq (by linarith : 0 ≤ 1+t)]
  ring_nf
  rfl

#print axioms zero_value
#print axioms zero_sob
#print axioms zero_mild
#print axioms zero_energy
end NSFormalization.Section4.A01
