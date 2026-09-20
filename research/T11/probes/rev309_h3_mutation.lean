import NSFormalization.Section3.T11.CriterionBridge

noncomputable section
namespace NSFormalization.Section3.T11.ReviewerMutation

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10
open NSFormalization.Paper1.PeriodicLocalLifespan
open scoped ENNReal

/-- Deliberately false strengthening: replace the H² lintegral by H³ while
keeping the H²-energy predicate. The reviewed theorem must not prove this. -/
example {ν S : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f S) :
    (∫⁻ t in Ioo (0 : ℝ) S,
        periodicSobolevENorm 3 (fun x ↦ w.velocity (t, x)) ^ 2) ≠ ⊤ ↔
      FiniteH2Energy (toFlow w) := by
  exact squaredHTwoIntegralT_ne_top_iff_finiteH2Energy w

end NSFormalization.Section3.T11.ReviewerMutation
