import NSFormalization.Section3.T10.Parseval
import NSFormalization.Section3.T10.DatumBasics
import NSFormalization.Section3.T12.MeanZeroCalculus

/-!
# Parseval at order zero

The order-zero periodic Sobolev extended norm is the physical torus `L²` norm.
The proof below deliberately keeps the infimum packaging visible: Parseval's
backward direction supplies one representing datum, `datum_unique` identifies
every other representing datum with it, and `parseval_forward` evaluates its
norm.
-/

noncomputable section

namespace NSFormalization.Section3.T15

open MeasureTheory
open NSFormalization.Section3.T10
open NSFormalization.Section3.T12 (SmoothPeriodicT)
open NSFormalization.Section4.A02 (SpatialField)
open NavierStokes.ProblemStatement
open scoped ContDiff ENNReal BigOperators

/-! ## The infimum collapses whenever an `L²` datum exists. -/

theorem periodicSobolevENorm_zero_eq_of_memLp (z : SpatialField)
    (hp : IsPeriodicSpatial z)
    (hz : MemLp (torusLift z) 2 periodicTorusMeasure) :
    periodicSobolevENorm 0 z = eLpNorm (torusLift z) 2 periodicTorusMeasure := by
  obtain ⟨A, hA⟩ := parseval_backward z hp hz
  have hdatum : periodicSobolevENorm 0 z = ‖A‖ₑ := by
    apply le_antisymm
    · exact iInf_le_of_le ⟨A, hA⟩ le_rfl
    · apply le_iInf
      intro B
      rw [datum_unique 0 z B.1 A B.2 hA]
  exact hdatum.trans (parseval_forward z A hA hz)

/-! ## Smooth fields supply the physical `L²` hypothesis. -/

private theorem memLp_torusLift_smooth {z : SpatialField}
    (hs : ContDiff ℝ ∞ z) :
    MemLp (torusLift z) 2 periodicTorusMeasure := by
  apply MemLp.of_eval_piLp
  intro i
  exact (NSFormalization.Paper1.memLp_torusLift
    (Complex.continuous_ofReal.comp
      ((PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ ℝ) i).comp hs.continuous)) 2).re

theorem periodicSobolevENorm_zero_eq (z : SpatialField) (hz : SmoothPeriodicT z) :
    periodicSobolevENorm 0 z = eLpNorm (torusLift z) 2 periodicTorusMeasure := by
  exact periodicSobolevENorm_zero_eq_of_memLp z hz.2 (memLp_torusLift_smooth hz.1)

theorem periodicSobolevENorm_zero_ne_top (z : SpatialField) (hz : SmoothPeriodicT z) :
    periodicSobolevENorm 0 z ≠ ⊤ := by
  rw [periodicSobolevENorm_zero_eq z hz]
  exact (memLp_torusLift_smooth hz.1).eLpNorm_lt_top.ne

end NSFormalization.Section3.T15
