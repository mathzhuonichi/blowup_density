import NSFormalization.Section3.T17.SlabBridge

/-! Negative regression probe: the requested positive classical-reference
bridge cannot be supplied for the unchanged API. The canonical module proves
that the exact proposed hypothesis block is insufficient. This file does not
assume a replacement bridge or claim to construct the requested correction. -/
open NSFormalization.Section3.T17 NSFormalization.Section3.T16

example : ¬ correctionStatementSlab := not_correctionStatementSlab

example : ¬ ∃ D : CutoffData,
    Nonempty (CorrectionAPI 1 Nonvacuity.place slabCounterexample (1 / 4) 1 D) := by
  rintro ⟨D, ⟨A⟩⟩
  exact slabCounterexample_not_periodic A.reference_periodic
