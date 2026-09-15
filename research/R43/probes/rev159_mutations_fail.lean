import NSFormalization.Section4.R43.Pieces

/-!
Reviewer 159 negative probe **A** — this file is EXPECTED TO FAIL to compile.

Mutation of `NSFormalization.Section4.R43.enorm_npow_two_eq_rpow_two` (G6):
the rpow exponent is changed from `2` to `3`.  The lemma's own proof script is
kept verbatim, so the failure is the mathematics, not a missing argument.
-/

open scoped ENNReal

theorem g6_mutated_rpow_three (x : ℝ≥0∞) : x ^ (2 : ℕ) = x ^ (3 : ℝ) := by
  rw [show (3 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
