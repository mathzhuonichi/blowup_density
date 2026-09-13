import NSFormalization.Paper1.PeriodicCriticalBridge

/-!
# Sharpness of the finite Cauchy--Schwarz bridge

The finite coefficient estimate is exact on constant coefficients with unit
weight.  Thus cardinality loss cannot be removed by rearranging that
finite-dimensional Cauchy--Schwarz step alone; a genuine critical argument
must use cancellation, spatial structure, or a different norm estimate.
-/
noncomputable section
namespace NSFormalization.Paper1

open NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open scoped BigOperators

/-- Unit constant coefficients attain equality in the finite weighted
Cauchy--Schwarz bound with unit weight. -/
theorem finite_coeff_l1_weightedEnergy_eq_for_const
    (S : Finset PeriodicFrequency) :
    (∑ k ∈ S, ‖(1 : ℂ)‖) =
      Real.sqrt (∑ k ∈ S, (1 : ℝ) * ‖(1 : ℂ)‖ ^ 2) *
        Real.sqrt (∑ k ∈ S, (1 : ℝ)⁻¹) := by
  simp [nsmul_eq_mul]

/-- The square-root cardinality factor in the unweighted estimate is sharp
for constant coefficients. -/
theorem finite_coeff_l1_eq_sqrt_card_mul_l2_for_const
    (S : Finset PeriodicFrequency) :
    (∑ k ∈ S, ‖(1 : ℂ)‖) =
      Real.sqrt (S.card : ℝ) *
        Real.sqrt (∑ k ∈ S, ‖(1 : ℂ)‖ ^ 2) := by
  simp [nsmul_eq_mul]

end NSFormalization.Paper1
