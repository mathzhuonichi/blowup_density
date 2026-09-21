import NSFormalization.Section3.T24.AffineBasics

noncomputable section

namespace NSFormalization.Section3.T24.Review392

open Set
open NavierStokes.ProblemStatement
open scoped ContDiff

/- A concrete allowed cylinder has an admissible perturbation (the zero field). -/
example :
    AffineAdmissible (0 : Space) 1 (1 / 4 : ℝ) (3 / 4 : ℝ)
      (fun _ : SpaceTime ↦ (0 : Space)) := by
  refine ⟨contDiff_const, HasCompactSupport.zero, ?_, ?_⟩
  · simp
  · intro t x
    simp [spatialDivergence, spatialDerivative]

/- The window itself is genuinely nonempty and satisfies the field theorem. -/
example : (0 : ℝ) < 1 / 4 ∧ (1 / 4 : ℝ) < 3 / 4 ∧ (3 / 4 : ℝ) < 1 := by
  exact window (by norm_num) (by norm_num) (by norm_num)

end NSFormalization.Section3.T24.Review392
