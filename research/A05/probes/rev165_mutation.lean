import NSFormalization.Section4.A05.CriticalL3

noncomputable section

open MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.D01.Homogeneous
open scoped ENNReal

namespace Review165Mutation

/-- Substantive mutation: replace the three-coordinate factor `3` by `2`. -/
def mutatedCriticalL3Const : ℝ :=
  2 * NSFormalization.Section4.A05.scalarCriticalConst (1 / 2)

example (z : NSFormalization.Section4.A02.SpatialField)
    (hz : NSFormalization.Section4.A02.MemHInfty z) :
    eLpNorm z 3 volume ≤
      ENNReal.ofReal mutatedCriticalL3Const *
        NSFormalization.Section4.A05.dotHomogeneousENorm (1 / 2) z := by
  exact NSFormalization.Section4.A05.velocityCriticalL3 z hz

end Review165Mutation
