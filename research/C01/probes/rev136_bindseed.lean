-- Reviewer probe (lane 136 review, REVIEW_E2.md), preserved verbatim; compiles on this branch.
import Contracts.V1.Data
import Contracts.V1.GradientL6
import NSFormalization.Section4.C01.Vocabulary

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace ContDiff

namespace Rev136Seed
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open EulerLpTranslation EulerOrdinarySobolev
open NSFormalization.Section4.C01

-- verbatim from research/C01/Spec.lean:166, 172, 185, 196
def slice (z : SpaceTimeField) (t : ℝ) : SpatialField := fun x => z (t, x)
def l2Sq (z : SpatialField) : ℝ := ∫ x : Space, ‖z x‖ ^ 2
def gradientSq (z : SpatialField) : ℝ := ∫ x : Space, ‖gradientTensor z x‖ ^ 2
def pairing (w z : SpatialField) : ℝ := ∫ x : Space, (inner ℝ (w x) (z x) : ℝ)

/-- the missing E2b tail, the one-line verification-side step -/
theorem gradientSq_eq_fderivSum (z : SpatialField) :
    gradientSq z = ∫ x : Space, ∑ i : Fin 3, ‖fderiv ℝ z x (axis i)‖ ^ 2 :=
  integral_congr_ae (Filter.Eventually.of_forall fun _ => PiLp.norm_sq_eq_of_L2 _ _)

/-- E2a at spec vocabulary -/
theorem spec_l2Sq_eq_inner (A : SmoothL2Field Space) :
    l2Sq A.field = ⟪A.toLp, A.toLp⟫ := l2Sq_eq_inner A

theorem spec_norm_toLp_sq (A : SmoothL2Field Space) : ‖A.toLp‖ ^ 2 = l2Sq A.field :=
  norm_toLp_sq_eq_l2Sq A

/-- E2b at spec vocabulary: the full chain -/
theorem spec_gradientSq_eq_sum (A : SmoothL2Field Space) :
    ∑ i : Fin 3, ‖(A.directionalField (axis i)).toLp‖ ^ 2 = gradientSq A.field :=
  (gradientSq_eq_sum A).trans (gradientSq_eq_fderivSum A.field).symm

/-- E2c at spec vocabulary -/
theorem spec_pairing_eq_inner (A B : SmoothL2Field Space) :
    pairing A.field B.field = ⟪A.toLp, B.toLp⟫ := pairing_eq_inner A B

/-- the spec's asserted derivative value, from the five carrier-B inputs -/
theorem spec_energyIdentity_value {ν d : ℝ} (u f Gt P : SmoothL2Field Space) (p : Space → ℝ)
    (hp : ContDiff ℝ ∞ p) (hgrad : ∀ x, P.field x = gradient p x)
    (hdiv : ∀ x, EulerSmoothLimit.divergence u.field x = 0)
    (hd : d = 2 * ⟪u.toLp, Gt.toLp⟫)
    (hmom : Gt.toLp
        = ν • (NSFormalization.Source.OrdinaryViscousStability.laplacianField u).toLp - (advectionField u u).toLp - P.toLp + f.toLp) :
    d = -2 * ν * gradientSq u.field + 2 * pairing u.field f.field := by
  rw [gradientSq_eq_fderivSum u.field]
  exact energyIdentity_of_carrierB u f Gt P p hp hgrad hdiv hd hmom

#print axioms gradientSq_eq_fderivSum
#print axioms spec_gradientSq_eq_sum
#print axioms spec_energyIdentity_value

end Rev136Seed
