import NSFormalization.Section3.T22.OrderZero
import NSFormalization.Section3.T22.CutoffMultiplierField
import NSFormalization.Section3.T22.ZeroExtensionComparison

/-!
# T22 assembly: bounded-domain Sobolev norm

The three canonical T22 fields are assembled here into the reconciled
`BoundedDomainNormAPI`.  The existential statement is kept as a separate alias
so the registration layer can expose the same proposition without importing a
proof-side namespace.
-/

noncomputable section

namespace NSFormalization.Section3.T22

open Set MeasureTheory
open NavierStokes.ProblemStatement
open Metric
open NSFormalization.Section4.A02 (SpatialField)
open scoped ContDiff ENNReal Topology

/-- The canonical bounded-domain norm API assembled from U-A5, U-A3 and U-Z1. -/
theorem boundedDomainNorm : BoundedDomainNormAPI :=
  ⟨orderZero, cutoffMultiplier, zeroExtensionComparison⟩

/-! Existential statement form used by the contract registration. -/
def boundedDomainNormStatement : Prop := Nonempty BoundedDomainNormAPI

theorem boundedDomainNormStatement_holds : boundedDomainNormStatement :=
  ⟨boundedDomainNorm⟩

/-! ## A concrete non-vacuity witness -/

def nonvacuityΩ : Set Space := Metric.ball (0 : Space) 1

def nonvacuityK : Set Space := Metric.closedBall (0 : Space) (1 / 2 : ℝ)

def nonvacuityBump : ContDiffBump (0 : Space) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

def nonvacuityField : SpatialField :=
  fun x => nonvacuityBump x • coordinateVector 0

theorem nonvacuityΩ_open : IsOpen nonvacuityΩ := isOpen_ball

theorem nonvacuityK_compact : IsCompact nonvacuityK := isCompact_closedBall _ _

theorem nonvacuityK_subset_Ω : nonvacuityK ⊆ nonvacuityΩ := by
  intro x hx
  have hxnorm : ‖x‖ ≤ (1 / 2 : ℝ) := by
    simpa [nonvacuityK, Metric.mem_closedBall, dist_zero_right] using hx
  have hxlt : ‖x‖ < (1 : ℝ) := lt_of_le_of_lt hxnorm (by norm_num)
  simpa [nonvacuityΩ, Metric.mem_ball, dist_zero_right] using hxlt

theorem nonvacuityField_contDiff : ContDiff ℝ ∞ nonvacuityField := by
  exact nonvacuityBump.contDiff.smul contDiff_const

theorem nonvacuityField_support :
    tsupport (zeroExtension nonvacuityΩ nonvacuityField) ⊆ nonvacuityK := by
  rw [tsupport]
  apply closure_minimal
  · intro x hx
    by_contra hxK
    apply hx
    by_cases hxΩ : x ∈ nonvacuityΩ
    · rw [zeroExtension, indicator_of_mem hxΩ]
      change nonvacuityBump x • coordinateVector 0 = 0
      have hxnorm : (1 / 2 : ℝ) < ‖x‖ := by
        have hnot : ¬ ‖x‖ ≤ (1 / 2 : ℝ) := by
          simpa [nonvacuityK, Metric.mem_closedBall, dist_zero_right] using hxK
        exact lt_of_not_ge hnot
      have hdist : nonvacuityBump.rOut ≤ dist x (0 : Space) := by
        simpa [nonvacuityBump, dist_zero_right] using (le_of_lt hxnorm)
      rw [nonvacuityBump.zero_of_le_dist hdist]
      simp
    · simp [zeroExtension, hxΩ]
  · exact isClosed_closedBall

theorem nonvacuityField_ne_zero : nonvacuityField 0 ≠ 0 := by
  rw [nonvacuityField]
  have hzero : (0 : Space) ∈ Metric.closedBall (0 : Space) nonvacuityBump.rIn := by
    simp [nonvacuityBump]
  rw [nonvacuityBump.one_of_mem_closedBall hzero, one_smul]
  intro h
  have hi := congrArg (fun x : Space => x 0) h
  simp [coordinateVector] at hi

/-- A nonzero smooth bump field on a compact ball strictly inside an open ball. -/
theorem boundedDomainNorm_nonvacuity :
    ∃ (Ω K : Set Space) (z : SpatialField),
      IsOpen Ω ∧ IsCompact K ∧ K ⊆ Ω ∧
        ContDiffOn ℝ ∞ z Ω ∧ tsupport (zeroExtension Ω z) ⊆ K ∧ z 0 ≠ 0 := by
  exact ⟨nonvacuityΩ, nonvacuityK, nonvacuityField,
    nonvacuityΩ_open, nonvacuityK_compact, nonvacuityK_subset_Ω,
    nonvacuityField_contDiff.contDiffOn, nonvacuityField_support,
    nonvacuityField_ne_zero⟩

end NSFormalization.Section3.T22
