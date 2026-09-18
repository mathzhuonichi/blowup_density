import NSFormalization.Section3.T13.WholeSpaceIdentity

noncomputable section

namespace NSFormalization.Section3.T13

open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section4.D01 (dotHomogeneousENorm)
open scoped ContDiff ENNReal BigOperators Topology

/- Substantive mutation: change the exact Fourier constant to `2 * cFrac s`.
   The shipped theorem must not close this altered statement. -/
example :
    ∀ (s : ℝ), 0 < s → s < 1 → ∀ f : SpatialField,
      ContDiff ℝ ∞ f → HasCompactSupport f →
        IReal s f < ⊤ ∧
          IReal s f = (2 : ℝ≥0∞) * cFrac s * dotHomogeneousENorm s f ^ (2 : ℕ) := by
  intro s hs0 hs1 f hzs hzc
  exact wholeSpace_identity s hs0 hs1 f hzs hzc

end NSFormalization.Section3.T13
