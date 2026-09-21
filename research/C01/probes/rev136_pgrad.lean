-- Reviewer probe (lane 136 review, REVIEW_E2.md), preserved verbatim; compiles on this branch.
import NSFormalization.Section4.C01.Vocabulary
noncomputable section
open MeasureTheory EulerLpTranslation EulerOrdinarySobolev EulerSmoothLimit
open scoped RealInnerProductSpace ContDiff
namespace Rev136PG

/-- the Ep side fact the next lane needs: the contracts' `∇p = ∑ᵢ(∂ᵢp)eᵢ` is Mathlib's
`gradient`, which is what `gradient_pairing_zero`'s `hgrad` slot asks for. -/
theorem pressureGradient_eq_gradient (p : Space → ℝ) (x : Space) :
    ∑ i : Fin 3, (fderiv ℝ p x (axis i)) • axis i = gradient p x := by
  refine PiLp.ext fun j => ?_
  have hg : (gradient p x).ofLp j = fderiv ℝ p x (axis j) := by
    rw [← inner_gradient_left (𝕜 := ℝ) (f := p) (x := x) (y := axis j), axis,
      EuclideanSpace.inner_single_right]
    simp
  simp [axis, hg, Pi.single_apply, mul_ite, Finset.sum_ite_eq']

#print axioms pressureGradient_eq_gradient
end Rev136PG
