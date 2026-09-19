import Bindings.BoundaryInsertion
import Bindings.InsertionFromData
import Bindings.Thresholds

/-! Supplier-only non-vacuity; this is not a boundary API witness. -/
noncomputable section
namespace T23U9Probe
open Set
open BlowupDensity.Contracts.V1
open scoped ContDiff

theorem supplier_nonempty :
    ∃ C : CorrectionAPI 1
      (BlowupDensity.Bindings.insertionFromData_packet 1 one_pos),
      C.T = 1 ∧ C.r = (1 / 4 : ℝ) := by
  obtain ⟨C, A, D, _, hT, _, _, hr, _⟩ :=
    BlowupDensity.Bindings.BoundaryInsertion.exists_matching_registered_cutoff
      (BlowupDensity.Bindings.insertionFromData_packet 1 one_pos)
      BlowupDensity.Bindings.thresholds (fun _ => 0) (0 : Space)
      (T := 1) (δ := 1) (r := 1 / 3) (ρ := 1 / 4)
      one_pos one_pos (by norm_num) (by norm_num) (by norm_num)
      contDiff_const.contDiffOn (by
        intro t ht x hx
        simp [spatialDivergence, spatialDerivative])
  exact ⟨C, hT, hr⟩

end T23U9Probe

/-- info: 'T23U9Probe.supplier_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms T23U9Probe.supplier_nonempty
