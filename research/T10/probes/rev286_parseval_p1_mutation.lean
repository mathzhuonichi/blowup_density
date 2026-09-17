import NSFormalization.Section3.T10.Parseval

noncomputable section
namespace NSFormalization.Section3.T10

open MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField)
open scoped ENNReal

-- Reviewer mutation: replacing the L² norm by L¹ must not be discharged by Parseval.
example :
    ∀ (z : SpatialField) (A : PeriodicSobolev 0), IsPeriodicDatum 0 z A →
      MemLp (torusLift z) 2 periodicTorusMeasure →
      ‖A‖ₑ = eLpNorm (torusLift z) 1 periodicTorusMeasure := parseval_forward

end NSFormalization.Section3.T10
