import NSFormalization.Section3.T18.SobolevRate

/-! Reviewer-only non-vacuity checks for lane 445. -/

noncomputable section
namespace NSFormalization.Section3.T18.Rev445

open Set
open NSFormalization.Section3.T10
open NSFormalization.Section3.T15

/-- The scale interval used by every U11 estimate is inhabited. -/
example (data : InsertionData) : ∃ ε : ℝ, ε ∈ Ioc (0 : ℝ) (ε₀ data) := by
  exact ⟨ε₀ data, eps_pos data, le_rfl⟩

/-- The positive-order honesty field is usable at an actual order and scale. -/
example (data : InsertionData) :
    MemForceSobolevT 1 0
      (fun z ↦ force data (ε₀ data) z - data.g z) := by
  exact forceDifference_sobolev_memLp data 0 (by norm_num) (by norm_num)
    (ε₀ data) ⟨eps_pos data, le_rfl⟩

/-- The negative-order honesty field is usable at an actual order and scale. -/
example (data : InsertionData) :
    MemForceSobolevT 1 (-1)
      (fun z ↦ force data (ε₀ data) z - data.g z) := by
  exact negative_s_memLp data (-1) (by norm_num)
    (ε₀ data) ⟨eps_pos data, le_rfl⟩

/-- The selected rate constant does not collapse under `ENNReal.ofReal`. -/
example (data : InsertionData) : 0 < forceDiffSobolevConst data 0 := by
  exact forceDiffSobolevConst_pos data 0 (by norm_num) (by norm_num)

end NSFormalization.Section3.T18.Rev445
