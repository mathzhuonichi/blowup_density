import NSFormalization.Section3.T11.H1Bridges
import NSFormalization.Section3.T11.EnstrophyInequality
import NSFormalization.Section3.T11.ClassicalRegularity
import NSFormalization.Section4.A04.EnstrophyBarrier

/-!
# Periodic H¹ restart adapters

The revised article `paper/revised/sections/02-preliminaries.tex:149–156` says
“For each initial velocity in the stated class and each force smooth into
every $H^m$ on compact time intervals” there is a maximal smooth velocity,
and “then it extends smoothly beyond $S$” under the squared H² criterion.
The separate uniform H¹ restart target is recorded in `research/P21/Targets.lean`.
This module retains the mean and uses the registered angular normalization κ=1.
-/
noncomputable section
namespace NSFormalization.Section3.T11
open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10 NSFormalization.Section3.T12
open T20 (lTwoSqT gradientSqT laplacianSqT)
open scoped ContDiff ENNReal BigOperators

/-- The gradient carrier in B2 is precisely the finite physical L² norm. -/
theorem periodicGradient_bridgeT {z : SpatialField} (hz : ContDiff ℝ ∞ z) :
    periodicLpENorm 2 (gradientTensor z) =
      ENNReal.ofReal (Real.sqrt (gradientSqT z)) := by
  rw [gradientSqT, Real.sqrt_sq ENNReal.toReal_nonneg]
  exact (ENNReal.ofReal_toReal (memLp_gradientTensor hz).2.ne).symm

end NSFormalization.Section3.T11
