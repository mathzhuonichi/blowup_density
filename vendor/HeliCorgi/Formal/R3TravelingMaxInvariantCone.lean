import Mathlib

/-!
# Traveling-max invariant-cone algebra

This file formalizes only the elementary real-algebra implications used in
`docs/gates/ASTRA_S15_TRAVELING_MAX_2026-09-05.md`.

There is deliberately **no** Navier--Stokes content here.  In particular this file does not
prove the moving-max identities, existence of a maximizer branch, either PDE boundary
barrier, finite-time blow-up, or any Clay alternative.  The open analytic statements stay
explicit in the research record.
-/

namespace MNS2

/-- Inside the proposed cone `q >= 1/4`, `d <= 1/8`, the normalized quadratic-growth
coefficient is at least `3/8`.  Multiplication by `A^2` is harmless because it is
nonnegative. -/
theorem travelingMax_growthCoefficient {A q d : ℝ}
    (hq : (1 : ℝ) / 4 ≤ q) (hd : d ≤ (1 : ℝ) / 8) :
    ((3 : ℝ) / 8) * A ^ 2 ≤ (2 * q - d) * A ^ 2 := by
  have hcoef : (3 : ℝ) / 8 ≤ 2 * q - d := by
    linarith
  exact mul_le_mul_of_nonneg_right hcoef (sq_nonneg A)

/-- The printed Q-barrier `Pi + e + (1/4)d + m >= 17/16` makes the normalized
`q`-boundary vector field inward at `q = 1/4`. -/
theorem travelingMax_qBoundary_inward {Pi e d m : ℝ}
    (hQ : (17 : ℝ) / 16 ≤ Pi + e + ((1 : ℝ) / 4) * d + m) :
    0 ≤ Pi - 1 - ((1 : ℝ) / 4) ^ 2 + e + ((1 : ℝ) / 4) * d + m := by
  norm_num at hQ ⊢
  linarith

/-- The printed D-barrier `h - 2e - f <= 1/32`, together with `q >= 1/4`, makes the
normalized `d`-boundary vector field inward at `d = 1/8`. -/
theorem travelingMax_dBoundary_inward {q e f h : ℝ}
    (hq : (1 : ℝ) / 4 ≤ q) (hD : h - 2 * e - f ≤ (1 : ℝ) / 32) :
    2 * ((1 : ℝ) / 8) ^ 2 - 2 * q * ((1 : ℝ) / 8) - 2 * e - f + h ≤ 0 := by
  norm_num at hq hD ⊢
  linarith

end MNS2
