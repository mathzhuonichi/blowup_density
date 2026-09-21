import Formal.R3SchwartzSobolevCore

namespace MNS2

noncomputable section

/--
A uniform one-coordinate Sobolev estimate for the three physical convection summands
`uᵢ ∂ᵢ v` on the Schwartz core.

This is strictly more local than `R3SchwartzConvectionSobolevEstimate`: it isolates the genuinely
analytic multiplication/derivative estimate from the finite-dimensional summation over `Fin 3`.
-/
def R3SchwartzConvectionTermSobolevEstimate (m : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin 3) (u v : R3SchwartzVelocity),
    ‖r3SchwartzToHsCLM ((m : ℝ) - 1) (r3SchwartzConvectionTerm i u v)‖ ≤
      C * ‖r3SchwartzToHsCLM (m : ℝ) u‖ * ‖r3SchwartzToHsCLM (m : ℝ) v‖

/--
A uniform Sobolev estimate for the three coordinate terms implies the full convection estimate.
The factor `3` is only the triangle-inequality cost of summing the three physical coordinates; no
analytic estimate is hidden in this reduction.
-/
theorem R3SchwartzConvectionTermSobolevEstimate.to_convection
    {m : ℕ} (h : R3SchwartzConvectionTermSobolevEstimate m) :
    R3SchwartzConvectionSobolevEstimate m := by
  rcases h with ⟨C, hC, hterm⟩
  refine ⟨3 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro u v
  calc
    ‖r3SchwartzToHsCLM ((m : ℝ) - 1) (r3SchwartzConvection u v)‖ =
        ‖∑ i : Fin 3,
          r3SchwartzToHsCLM ((m : ℝ) - 1) (r3SchwartzConvectionTerm i u v)‖ := by
      simp [r3SchwartzConvection]
    _ ≤ ∑ i : Fin 3,
        ‖r3SchwartzToHsCLM ((m : ℝ) - 1) (r3SchwartzConvectionTerm i u v)‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3,
        C * ‖r3SchwartzToHsCLM (m : ℝ) u‖ * ‖r3SchwartzToHsCLM (m : ℝ) v‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact hterm i u v
    _ = (3 * C) * ‖r3SchwartzToHsCLM (m : ℝ) u‖ *
        ‖r3SchwartzToHsCLM (m : ℝ) v‖ := by
      simp
      ring

end

end MNS2
