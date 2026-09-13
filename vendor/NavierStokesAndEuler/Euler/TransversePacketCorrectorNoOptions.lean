import Euler.TransversePacketCorrector

/-!
# `Data.potentialCoefficientPath_time` at default recursion depth

This separate namespace reuses the original definitions and proves the same statement
from `Data.potential_hasDerivWithinAt`. It changes only the derivative value using
`HasDerivWithinAt.congr_deriv` and the interval projection identity.

The original `simpa only` proof exceeds the default recursion depth in an isolated
reproduction. The proof below passes with default resource limits and the Euler
library's strict compiler options:
`lake env lean -DautoImplicit=false -DwarningAsError=true Euler/TransversePacketCorrectorNoOptions.lean`
-/

noncomputable section

namespace EulerTransversePacketProvider.Data.NoRecDepth

open Set EulerSmoothLimit EulerSourcePotentialCoefficient EulerVolterraConvolution
open scoped BoundedContinuousFunction

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] (D : Data U)

private local instance : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance
private local instance : NormedAddCommGroup PotentialField := inferInstance
private local instance : NormedSpace ℝ PotentialField := inferInstance
private local instance : NormedAddCommGroup C(Icc (0 : ℝ) D.T,PotentialField) := inferInstance
private local instance : NormedSpace ℝ C(Icc (0 : ℝ) D.T,PotentialField) := inferInstance

theorem potentialCoefficientPath_time (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D.T) (x : Space) :
    HasDerivWithinAt (fun r => extendPath D.T D.T_pos.le D.potentialCoefficientPath r x)
      (extendPath D.T D.T_pos.le D.potentialDerivative t x) (Icc (0 : ℝ) D.T) t := by
  exact (D.potential_hasDerivWithinAt ⟨t, ht⟩ x).congr_deriv
    (congrArg (fun s : Icc (0 : ℝ) D.T => D.potentialDerivative s x)
      (projIcc_of_mem D.T_pos.le ht).symm)

end EulerTransversePacketProvider.Data.NoRecDepth
