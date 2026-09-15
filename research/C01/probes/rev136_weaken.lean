-- Reviewer probe (lane 136 review, REVIEW_E2.md), preserved verbatim; compiles on this branch.
import NSFormalization.Section4.C01.Vocabulary
noncomputable section
open MeasureTheory EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
  EulerSmoothLimit NSFormalization.Source.OrdinaryViscousStability
open scoped RealInnerProductSpace ContDiff
namespace Rev136W
open NSFormalization.Section4.C01

set_option autoImplicit false in
/-- same conclusion with `hp` weakened from `ContDiff ℝ ∞ p` to `Differentiable ℝ p` -/
theorem energyIdentity_of_carrierB' {ν d : ℝ} (u f Gt P : SmoothL2Field Space) (p : Space → ℝ)
    (hp : Differentiable ℝ p) (hgrad : ∀ x, P.field x = gradient p x)
    (hdiv : ∀ x, divergence u.field x = 0)
    (hd : d = 2 * ⟪u.toLp, Gt.toLp⟫)
    (hmom : Gt.toLp
        = ν • (laplacianField u).toLp - (advectionField u u).toLp - P.toLp + f.toLp) :
    d = -2 * ν * (∫ x, ∑ i : Fin 3, ‖fderiv ℝ u.field x (axis i)‖ ^ 2)
          + 2 * (∫ x, ⟪u.field x, f.field x⟫) :=
  energyIdentity_of_carrierB u f Gt P p (potential_smooth P p hp hgrad) hgrad hdiv hd hmom

#print axioms energyIdentity_of_carrierB'
end Rev136W
