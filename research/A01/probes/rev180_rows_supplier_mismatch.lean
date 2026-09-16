import NSFormalization.Section4.A01.ConstructorAssembly
import NSFormalization.Section4.A01.JointRepresentative

/-! Historical negative probe for the rejected consumer shape: the landed
lane-190 theorem needs the all-order paths of the selected carrier and cannot
inhabit a representative supplier for every continuous L2 path without that
premise.  The corrected `rows_from_constructor_full` no longer asks for this
type. -/

noncomputable section

namespace Rev180RowsSupplierMismatch

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.A01
open NSFormalization.Section4.A02 (SpaceTimeField)
open scoped ContDiff

example {S : ℝ} (hS : 0 < S) :
    ∀ U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2),
      ∃ velocity : SpaceTimeField,
        (∀ t : Icc (0 : ℝ) S,
          (fun x : Space => velocity (t.1, x)) =ᵐ[volume] ⇑(U t)) ∧
        ContDiffOn ℝ ∞ velocity (Ico (0 : ℝ) S ×ˢ (univ : Set Space)) := by
  exact exists_joint_smooth_representative hS

end Rev180RowsSupplierMismatch
