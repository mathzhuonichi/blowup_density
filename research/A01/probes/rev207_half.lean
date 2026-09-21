import NSFormalization.Section4.A01.TameAssembly
noncomputable section
namespace NSFormalization.Section4.A01
open MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev EulerPressureSpatialRegularity EulerMildTopWord
  EulerSobolevWordBlocks EulerSobolevL2Product
open Finset
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

open EulerMetricTransport EulerSobolevWordLevel EulerRealCylinder EulerVectorCylinder EulerTransportDerivatives EulerH6Nonlinear EulerSobolevTransport EulerFiniteMetricEnergy
open scoped ContDiff
def rev207_halfConstant (q : ℕ) : ℝ :=
  (Fintype.card (SobolevWord (q+1)) : ℝ) * (2:ℝ)^(q+1) * sobolevEmbeddingConstant 1 3 / 2

open EulerFiniteMetricEnergy
/-- Unconditional smooth-cylinder coordinate tame estimate, with an explicit constant. -/
theorem rev207_halfTame {q : ℕ} (hq : 6 ≤ q) :
    SmoothCylinderCoordinateTame q hq (rev207_halfConstant q) := by
  intro V f hV hf _hfL i
  apply (familyNorm_le_sum_norm _).trans
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (SobolevWord (q+1))))
    (fun w _ => cylinderCoordinateWord_bound hq V f hV hf i w)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    rev207_halfConstant, mul_assoc] using hsum


end NSFormalization.Section4.A01
