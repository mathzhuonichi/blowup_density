import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Paper 3 threshold arithmetic and the valid intermediate negative Sobolev index.
These lemmas do not claim a Sobolev norm estimate or a Navier--Stokes density theorem. -/

noncomputable section

namespace NSFormalization.Paper3

/-- Parabolic force exponent for a three-dimensional Sobolev norm. -/
def forceExponent (q s : ℝ) : ℝ := 2 / q - 3 / 2 - s

theorem forceExponent_pos_iff (q s : ℝ) :
    0 < forceExponent q s ↔ s < 2 / q - 3 / 2 := by
  exact sub_pos

theorem forceExponent_one (s : ℝ) : forceExponent 1 s = 1 / 2 - s := by
  unfold forceExponent
  ring

theorem forceExponent_two (s : ℝ) : forceExponent 2 s = -1 / 2 - s := by
  unfold forceExponent
  ring

/-- Every index below the second threshold is dominated by a valid homogeneous
index strictly between −3/2 and −1/2. This avoids invalid low-frequency scaling. -/
theorem negative_intermediate_index {s : ℝ} (hs : s < -1 / 2) :
    ∃ r : ℝ, -3 / 2 < r ∧ r < -1 / 2 ∧ s < r := by
  refine ⟨(max s (-3 / 2) + (-1 / 2)) / 2, ?_⟩
  have hm : max s (-3 / 2) < (-1 / 2 : ℝ) := max_lt hs (by norm_num)
  have h₁ := le_max_left s (-3 / 2 : ℝ)
  have h₂ := le_max_right s (-3 / 2 : ℝ)
  constructor
  · linarith
  constructor <;> linarith

/-- The energy-force indices are strictly below their respective thresholds. -/
theorem energy_force_exponents :
    forceExponent 1 0 = 1 / 2 ∧ forceExponent 2 (-1) = 1 / 2 := by
  norm_num [forceExponent]

end NSFormalization.Paper3
