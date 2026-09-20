import NSFormalization.Section3.T22.OrderZeroIsometry

/-! Reviewer mutation probe: changing the target constant from `1` to `2` must
    make the delivered theorem inapplicable.  This file is intentionally not a
    successful Lean module; the expected type mismatch is recorded in the review. -/

noncomputable section
namespace Rev387Mutation

open MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section3.T22 NSFormalization.Section4.D01

example {z : Space → Space} (hz : MemLp z 2 volume) :
    ‖orderZeroDatum hz‖ₑ = 2 * eLpNorm z 2 volume := by
  exact norm_orderZeroDatum_eq hz

end Rev387Mutation
