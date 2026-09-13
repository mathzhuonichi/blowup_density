import Formal.R3SchwartzConvectionH3Closure
import Formal.R3SchwartzConvectionSobolevReduction

namespace MNS2

noncomputable section

/--
A uniform, non-sharp upper bound for the three coordinate-derivative Fourier constants.

The finite sum is used only to package the already proved coordinatewise estimates over `Fin 3`;
no new analytic estimate is introduced here.
-/
def r3UniformCoordinateDerivativeFrequencyConstant : ℝ :=
  ∑ i : Fin 3, r3CoordinateDerivativeFrequencyConstant i

theorem r3UniformCoordinateDerivativeFrequencyConstant_nonneg :
    0 ≤ r3UniformCoordinateDerivativeFrequencyConstant := by
  unfold r3UniformCoordinateDerivativeFrequencyConstant
  exact Finset.sum_nonneg fun i _ => r3CoordinateDerivativeFrequencyConstant_nonneg i

theorem r3CoordinateDerivativeFrequencyConstant_le_uniform (i : Fin 3) :
    r3CoordinateDerivativeFrequencyConstant i ≤
      r3UniformCoordinateDerivativeFrequencyConstant := by
  unfold r3UniformCoordinateDerivativeFrequencyConstant
  exact Finset.single_le_sum
    (fun j _ => r3CoordinateDerivativeFrequencyConstant_nonneg j)
    (Finset.mem_univ i)

/-- The explicit common constant in the uniform `H³ × H³ → H²` convection-term estimate. -/
def r3SchwartzConvectionH3Constant : ℝ :=
  4 * ‖r3H2InverseBesselWeightL2‖ * r3UniformCoordinateDerivativeFrequencyConstant

theorem r3SchwartzConvectionH3Constant_nonneg :
    0 ≤ r3SchwartzConvectionH3Constant := by
  unfold r3SchwartzConvectionH3Constant
  exact mul_nonneg
    (mul_nonneg (by norm_num) (norm_nonneg r3H2InverseBesselWeightL2))
    r3UniformCoordinateDerivativeFrequencyConstant_nonneg

/-- The uniform coordinate-term estimate with its exported explicit constant. -/
theorem norm_r3SchwartzToHsCLM_two_convectionTerm_le_H3_uniform
    (i : Fin 3) (u v : R3SchwartzVelocity) :
    ‖r3SchwartzToHsCLM 2 (r3SchwartzConvectionTerm i u v)‖ ≤
      r3SchwartzConvectionH3Constant *
        ‖r3SchwartzToHsCLM 3 u‖ * ‖r3SchwartzToHsCLM 3 v‖ := by
  have hconstant :
      4 * ‖r3H2InverseBesselWeightL2‖ * r3CoordinateDerivativeFrequencyConstant i ≤
        r3SchwartzConvectionH3Constant := by
    unfold r3SchwartzConvectionH3Constant
    exact mul_le_mul_of_nonneg_left
      (r3CoordinateDerivativeFrequencyConstant_le_uniform i)
      (mul_nonneg (by norm_num) (norm_nonneg r3H2InverseBesselWeightL2))
  calc
    ‖r3SchwartzToHsCLM 2 (r3SchwartzConvectionTerm i u v)‖ ≤
        4 * ‖r3H2InverseBesselWeightL2‖ *
          r3CoordinateDerivativeFrequencyConstant i *
          ‖r3SchwartzToHsCLM 3 u‖ * ‖r3SchwartzToHsCLM 3 v‖ :=
      norm_r3SchwartzToHsCLM_two_convectionTerm_le_H3 i u v
    _ ≤ r3SchwartzConvectionH3Constant *
          ‖r3SchwartzToHsCLM 3 u‖ * ‖r3SchwartzToHsCLM 3 v‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hconstant (norm_nonneg _))
        (norm_nonneg _)

/--
The coordinatewise `H³ × H³ → H²` estimate, packaged with one constant valid for every
physical coordinate.
-/
theorem r3SchwartzConvectionTermSobolevEstimate_three :
    R3SchwartzConvectionTermSobolevEstimate 3 := by
  refine ⟨r3SchwartzConvectionH3Constant,
    r3SchwartzConvectionH3Constant_nonneg, ?_⟩
  intro i u v
  have horder : ((3 : ℕ) : ℝ) - 1 = 2 := by norm_num
  have hthree : ((3 : ℕ) : ℝ) = 3 := by norm_num
  rw [horder, hthree]
  exact norm_r3SchwartzToHsCLM_two_convectionTerm_le_H3_uniform i u v

/-- The explicit constant for the full three-coordinate convection estimate. -/
def r3SchwartzConvectionFullH3Constant : ℝ :=
  3 * r3SchwartzConvectionH3Constant

theorem r3SchwartzConvectionFullH3Constant_nonneg :
    0 ≤ r3SchwartzConvectionFullH3Constant := by
  exact mul_nonneg (by norm_num) r3SchwartzConvectionH3Constant_nonneg

/-- The full Schwartz-core `H³ × H³ → H²` bound with its explicit constant. -/
theorem norm_r3SchwartzToHsCLM_two_convection_le_H3
    (u v : R3SchwartzVelocity) :
    ‖r3SchwartzToHsCLM 2 (r3SchwartzConvection u v)‖ ≤
      r3SchwartzConvectionFullH3Constant *
        ‖r3SchwartzToHsCLM 3 u‖ * ‖r3SchwartzToHsCLM 3 v‖ := by
  calc
    ‖r3SchwartzToHsCLM 2 (r3SchwartzConvection u v)‖ =
        ‖∑ i : Fin 3,
          r3SchwartzToHsCLM 2 (r3SchwartzConvectionTerm i u v)‖ := by
      simp [r3SchwartzConvection]
    _ ≤ ∑ i : Fin 3,
        ‖r3SchwartzToHsCLM 2 (r3SchwartzConvectionTerm i u v)‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3,
        r3SchwartzConvectionH3Constant *
          ‖r3SchwartzToHsCLM 3 u‖ * ‖r3SchwartzToHsCLM 3 v‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact norm_r3SchwartzToHsCLM_two_convectionTerm_le_H3_uniform i u v
    _ = r3SchwartzConvectionFullH3Constant *
        ‖r3SchwartzToHsCLM 3 u‖ * ‖r3SchwartzToHsCLM 3 v‖ := by
      simp [r3SchwartzConvectionFullH3Constant]
      ring

/-- The full three-coordinate Schwartz convection estimate at Sobolev order three. -/
theorem r3SchwartzConvectionSobolevEstimate_three :
    R3SchwartzConvectionSobolevEstimate 3 := by
  refine ⟨r3SchwartzConvectionFullH3Constant,
    r3SchwartzConvectionFullH3Constant_nonneg, ?_⟩
  intro u v
  have horder : ((3 : ℕ) : ℝ) - 1 = 2 := by norm_num
  have hthree : ((3 : ℕ) : ℝ) = 3 := by norm_num
  rw [horder, hthree]
  exact norm_r3SchwartzToHsCLM_two_convection_le_H3 u v

end

end MNS2
