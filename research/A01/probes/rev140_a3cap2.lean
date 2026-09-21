-- Reviewer probe (lane 140 review, REVIEW_EULER_PAIRING.md), preserved verbatim; compiles on this branch.
import NSFormalization.Section4.A01.EulerPairing
import NSFormalization.Section4.A04.Forcing

open NSFormalization.Section4.A01 NSFormalization.Section4.D01 NSFormalization.Section4.A04
open NSFormalization.Section4.A02 (SpaceTimeField)
open MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3 (RealVectorSobolev)
open EulerCylinderSobolevSpace EulerMeanOrdinaryLift
open scoped ENNReal

/-! ### THE VACUITY TRAP (before lane 140): no datum ⟹ `sobolevENorm = ⊤` ⟹ `sobolevNormAt = 0`. -/
theorem trap_enorm (s : ℝ) (z : Space → Space)
    (hempty : IsEmpty {A : RealVectorSobolev s // IsSobolevDatum s z A}) :
    sobolevENorm s z = ⊤ := by
  simp only [sobolevENorm, iInf_of_isEmpty, sInf_empty]

theorem trap_normAt (s : ℝ) (u : SpaceTimeField) (t : ℝ)
    (hempty : IsEmpty
      {A : RealVectorSobolev s // IsSobolevDatum s (fun x : Space => u (t, x)) A}) :
    sobolevNormAt s u t = 0 := by
  simp only [sobolevNormAt, trap_enorm s _ hempty, ENNReal.toReal_top]

/-! ### AFTER lane 140: at order 2 the datum exists, so the norm is genuinely finite. -/
theorem sobolevENorm_two_finite {q : ℕ} (u : SobolevSpace 1 (q + 1))
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u = u)
    (U : EulerMeanSolenoidal.L2) (hU : ordinaryLift U = value 1 u) (hq : 4 ≤ q) :
    sobolevENorm (2 : ℝ) (⇑U) ≠ ⊤ := by
  obtain ⟨A, hA⟩ := exists_isSobolevDatum_m_of_cylinder u hu U hU 2 (by omega)
  rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num] at hA
  rw [sobolevENorm_eq hA]
  exact enorm_ne_top

/-- `sobolevNormAt 2` of the velocity slice is the honest `‖A‖`, not junk `0`. -/
theorem sobolevNormAt_two_eq {q : ℕ} (u : SobolevSpace 1 (q + 1))
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u = u)
    (U : EulerMeanSolenoidal.L2) (hU : ordinaryLift U = value 1 u) (hq : 4 ≤ q)
    (v : SpaceTimeField) (t : ℝ) (hv : (fun x : Space => v (t, x)) = ⇑U) :
    ∃ A : RealVectorSobolev (2 : ℝ), IsSobolevDatum (2 : ℝ) (⇑U) A ∧
      sobolevNormAt 2 v t = ‖A‖ := by
  obtain ⟨A, hA⟩ := exists_isSobolevDatum_m_of_cylinder u hu U hU 2 (by omega)
  rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num] at hA
  refine ⟨A, hA, ?_⟩
  rw [sobolevNormAt, hv, sobolevENorm_eq hA]
  simp

#print axioms trap_normAt
#print axioms sobolevENorm_two_finite
#print axioms sobolevNormAt_two_eq
