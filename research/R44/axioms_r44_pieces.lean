import NSFormalization.Section4.R44.Pieces

/-!
Conformance probe for `NSFormalization.Section4.R44.Pieces`.

Every `#print axioms` below must report exactly
`[propext, Classical.choice, Quot.sound]`.  The examples instantiate every new
R44 theorem at concrete data and also exercise the two R43 results reused here.
-/

open Set intervalIntegral MeasureTheory
open scoped ENNReal
open NSFormalization.Section4.R44

#print axioms exists_rcritical2_constants
#print axioms radius_forces_gronwall_small
#print axioms criticalSquaredNormBound_radius

/-! ## Non-vacuity witnesses for the new declarations -/

example : ∃ theta c C : ℝ,
    0 < theta ∧ 0 < c ∧ 0 < C ∧
    1 * theta < 1 / 4 ∧ 1 * 1 * theta ≤ 1 / 4 ∧
    1 * c ^ 2 < theta ^ 2 / 4 ∧ C = 0 + 1 :=
  exists_rcritical2_constants (C₀ := 1) (C₁ := 1) (Cemb := 1)
    (C₂ := 0) (C₃ := 1) one_pos one_pos one_pos (by norm_num) one_pos

example : (1 : ℝ) * (1 : ℝ)⁻¹ * 0 ^ 2 * Real.exp (0 * 1 * 1) <
    ((1 : ℝ) * 1) ^ 2 / 4 :=
  radius_forces_gronwall_small (nu := 1) (S := 1) (theta := 1)
    (c := 1 / 4) (C₂ := 0) (C₃ := 1) (F := 0)
    one_pos (by norm_num) (by norm_num) one_pos (by norm_num)
    (by norm_num) (by norm_num) (by positivity)

example : ∀ t ∈ Icc (0 : ℝ) 1,
    (fun _ : ℝ => (0 : ℝ)) t ≤ (1 : ℝ) * 1 / 2 :=
  criticalSquaredNormBound_radius
    (T := 1) (nu := 1) (theta := 1) (C₂ := 0) (C₃ := 0) (R := 0)
    (Y := fun _ => 0) (E' := fun _ => 0) (Z := fun _ => 0) (B := fun _ => 0)
    (by norm_num) one_pos one_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) continuous_const rfl (fun _ _ => by norm_num)
    continuousOn_const (fun _ _ => by norm_num)
    (fun _ _ => by simpa using (hasDerivAt_const _ (0 : ℝ)))
    intervalIntegrable_const
    (fun _ _ _ => by norm_num)

/-! ## The two identical R43 rows are reused, not redeclared -/

#print axioms NSFormalization.Section4.R43.enorm_npow_two_eq_rpow_two
#print axioms NSFormalization.Section4.R43.criticalL3_gate_enorm

example : (3 : ℝ≥0∞) ^ (2 : ℕ) = (3 : ℝ≥0∞) ^ (2 : ℝ) :=
  NSFormalization.Section4.R43.enorm_npow_two_eq_rpow_two 3

example : ENNReal.ofReal (1 : ℝ) * ENNReal.ofReal (1 / 8) ≤ ENNReal.ofReal (1 / 4) :=
  NSFormalization.Section4.R43.criticalL3_gate_enorm
    (C₁ := 1) (Cemb := 1) (c := 1 / 8) (ν := 1) (y := 1 / 8)
    (L3 := ENNReal.ofReal (1 / 8))
    (by norm_num) (by norm_num) one_pos (by norm_num)
    (ENNReal.ofReal_le_ofReal (by norm_num)) (by norm_num)
