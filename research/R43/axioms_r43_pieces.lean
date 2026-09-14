import NSFormalization.Section4.R43.Pieces

/-!
Conformance probe for `NSFormalization.Section4.R43.Pieces`.

Each `#print axioms` must report exactly `[propext, Classical.choice, Quot.sound]`.
The examples below are non-vacuity witnesses: they instantiate the lemmas at
concrete data so that a vacuous or `True`-shaped statement would be visible.
Run: `cd verification && lake env lean ../research/R43/axioms_r43_pieces.lean`.
-/

open Set
open scoped ENNReal
open NSFormalization.Section4.R43

#print axioms enorm_npow_two_eq_rpow_two
#print axioms exists_critical_radius
#print axioms criticalL3_gate_real
#print axioms criticalL3_gate_enorm
#print axioms criticalNormBound_radius

/-! ## Non-vacuity witnesses -/

-- G6 is a genuine rewrite: both sides are the concrete value `9` at `x = 3`.
example : (3 : ℝ≥0∞) ^ (2 : ℕ) = (3 : ℝ≥0∞) ^ (2 : ℝ) :=
  enorm_npow_two_eq_rpow_two 3
example : (3 : ℝ≥0∞) ^ (2 : ℕ) = 9 := by norm_num

-- G8a produces an actual positive radius for concrete C₀ = C₁ = Cemb = 1:
-- the three conclusions are all non-trivial (0 < c, c < 1/4, c ≤ 1/4).
example : ∃ c : ℝ, 0 < c ∧ c < 1 / (4 * 1) ∧ 1 * 1 * c ≤ 1 / 4 :=
  exists_critical_radius (C₀ := 1) (C₁ := 1) (Cemb := 1) one_pos one_pos one_pos

-- G8b/G8c fire at concrete data (C₁ = Cemb = 1, c = 1/8, ν = 1, y = 1/8, L3 = 1/8):
-- the gate `1 * (1/8) ≤ 1/4` is a true but non-trivial inequality.
example : (1 : ℝ) * (1 / 8) ≤ 1 / 4 :=
  criticalL3_gate_real (C₁ := 1) (Cemb := 1) (c := 1 / 8) (ν := 1) (y := 1 / 8) (L3 := 1 / 8)
    (by norm_num) (by norm_num) one_pos (by norm_num) (by norm_num) (by norm_num)

example : ENNReal.ofReal (1 : ℝ) * ENNReal.ofReal (1 / 8) ≤ ENNReal.ofReal (1 / 4) :=
  criticalL3_gate_enorm (C₁ := 1) (Cemb := 1) (c := 1 / 8) (ν := 1) (y := 1 / 8)
    (L3 := ENNReal.ofReal (1 / 8))
    (by norm_num) (by norm_num) one_pos (by norm_num)
    (ENNReal.ofReal_le_ofReal (by norm_num)) (by norm_num)

-- S2 at the constant solution y ≡ 0 on [0,1] with ν = 1, C₀ = 1, c = 1/4, b ≡ 0, z ≡ 0:
-- eq:Rcritical1 holds (0 ≤ 0) and the conclusion `0 ≤ (1/4)*1` is real content.
example : ∀ t ∈ Icc (0 : ℝ) 1, (fun _ : ℝ => (0 : ℝ)) t ≤ (1 / 4) * 1 :=
  criticalNormBound_radius (T := 1) (ν := 1) (C₀ := 1) (c := 1 / 4)
    (y := fun _ => 0) (E' := fun _ => 0) (z := fun _ => 0) (b := fun _ => 0)
    (N := fun _ => 0)
    one_pos one_pos (by norm_num) (by norm_num)
    continuous_const rfl (fun _ _ => le_rfl)
    continuousOn_const rfl (fun _ _ => by norm_num)
    (fun _ _ => le_rfl)
    (fun _ _ => by simpa using (hasDerivAt_const _ (0 : ℝ)))
    (fun _ _ => hasDerivAt_const _ 0)
    (fun _ _ => by norm_num)
