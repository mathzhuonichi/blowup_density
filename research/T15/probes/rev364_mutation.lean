import NSFormalization.Section3.T15.HaarBridge

/-
Reviewer negative probe: change the main bridge's right-hand side by a
nontrivial constant factor.  The original theorem must not close this mutated
statement.  This file is intentionally expected to fail to typecheck.
-/

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13
open NSFormalization.Section3.T15
open scoped ContDiff ENNReal

example (f : SpatialField) (hf : ContDiff ℝ ∞ f)
    (hsupp : tsupport f ⊆ interior fundamentalCube) :
    eLpNorm (torusLift (periodize f)) 2 periodicTorusMeasure
      = 2 * eLpNorm f 2 volume := by
  exact eLpNorm_torusLift_periodize f hf hsupp
