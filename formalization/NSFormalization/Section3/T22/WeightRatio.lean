import NSFormalization.Paper3.SobolevHilbertModel

/-!
# T22 U-A1 — Peetre's weight-ratio inequality (`03-torus.tex:616-624`)

The fixed-cutoff `H^s(ℝ³)` multiplier bound of `cutoffMultiplier`
(`research/T22/Spec.lean:140-144`, unit `U-A3`) needs to dominate the output
inhomogeneous Sobolev weight `(1+‖ξ‖²)^{s/2}` by the input weight
`(1+‖η‖²)^{s/2}` times a power of the kernel weight `(1+‖ξ-η‖²)^{|s|/2}`.
This module supplies exactly that pointwise inequality, **Peetre's
inequality**, with the explicit constant `2^{|s|/2}`:

`(1+‖ξ‖²)^{s/2} ≤ 2^{|s|/2} · (1+‖η‖²)^{s/2} · (1+‖ξ-η‖²)^{|s|/2}`, for all real `s`.

## Route (`research/T22/T22_SPLIT.md`, unit `U-A1`)

1. `one_add_normSq_le`: the base submultiplicativity of the Japanese bracket
   `1 + ‖ξ‖² ≤ 2 (1+‖η‖²)(1+‖ξ-η‖²)`, from `‖ξ‖ ≤ ‖η‖ + ‖ξ-η‖` and
   `(a+b)² ≤ 2(a²+b²)`.
2. `rpow_base_le`: raise (1) to a **nonnegative** power `t/2` by `Real.rpow`
   monotonicity (`Real.rpow_le_rpow`) and split with `Real.mul_rpow`.
3. `weight_ratio_le`: for `s ≥ 0` apply (2) with `t = s`; for `s < 0` apply (2)
   to the swapped pair `(η, ξ)` with `t = -s` and invert (the negative-order
   power is the reciprocal, cleared by `Real.rpow_add`).

The last inequality is the same shape lane 342 proved on the integer lattice
`ℤ³` (`Section3/T11/PairingBound.lean:235`, `torusWeightPeetre`); here it is on
the continuous weight `(1+‖·‖²)^{s/2}` for **real** `s`, in the exact spelling
of the datum-layer weight `NSFormalization.Paper3.sobolevBesselWeight`
(`Paper3/SobolevHilbertModel.lean:24`,
`sobolevBesselWeight s ξ = ((1+‖ξ‖²)^{s/2} : ℝ)`), whose real magnitude is
provided in `sobolevBesselWeight_norm` so `U-A3` can apply this bound without
conversion.
-/

noncomputable section

namespace NSFormalization.Section3.T22

open NavierStokes.ProblemStatement (Space)
open NSFormalization.Paper3 (sobolevBesselWeight)

/-- Peetre's constant `2^{|s|/2}`. -/
def peetreConst (s : ℝ) : ℝ := (2 : ℝ) ^ (|s| / 2)

theorem peetreConst_pos (s : ℝ) : 0 < peetreConst s := by
  unfold peetreConst; positivity

/-- **Base Peetre submultiplicativity of the Japanese bracket.**
`1 + ‖ξ‖² ≤ 2 (1 + ‖η‖²)(1 + ‖ξ - η‖²)`, from the triangle inequality
`‖ξ‖ ≤ ‖η‖ + ‖ξ - η‖` and `(a+b)² ≤ 2(a²+b²)`. -/
theorem one_add_normSq_le (ξ η : Space) :
    1 + ‖ξ‖ ^ 2 ≤ 2 * (1 + ‖η‖ ^ 2) * (1 + ‖ξ - η‖ ^ 2) := by
  have hcancel : η + (ξ - η) = ξ := by abel
  have htri : ‖ξ‖ ≤ ‖η‖ + ‖ξ - η‖ := by
    have h := norm_add_le η (ξ - η)
    rwa [hcancel] at h
  have hsq : ‖ξ‖ ^ 2 ≤ (‖η‖ + ‖ξ - η‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) htri 2
  nlinarith [hsq, sq_nonneg (‖η‖ - ‖ξ - η‖), sq_nonneg (‖η‖ * ‖ξ - η‖),
    norm_nonneg η, norm_nonneg (ξ - η)]

/-- **Peetre raise at a nonnegative exponent.** Raising the base
submultiplicativity `1 + ‖ξ‖² ≤ 2(1+‖η‖²)(1+‖ξ-η‖²)` to the nonnegative power
`t/2` and splitting the product. Used for both signs of the order in
`weight_ratio_le`. -/
theorem rpow_base_le {t : ℝ} (ht : 0 ≤ t) (ξ η : Space) :
    (1 + ‖ξ‖ ^ 2) ^ (t / 2) ≤
      2 ^ (t / 2) * (1 + ‖η‖ ^ 2) ^ (t / 2) * (1 + ‖ξ - η‖ ^ 2) ^ (t / 2) := by
  have hbase := one_add_normSq_le ξ η
  have ht2 : (0 : ℝ) ≤ t / 2 := by linarith
  have hmono :
      (1 + ‖ξ‖ ^ 2) ^ (t / 2) ≤
        (2 * (1 + ‖η‖ ^ 2) * (1 + ‖ξ - η‖ ^ 2)) ^ (t / 2) :=
    Real.rpow_le_rpow (by positivity) hbase ht2
  rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by norm_num) (by positivity)] at hmono
  exact hmono

/-- **Peetre's weight-ratio inequality** (`03-torus.tex:616-624`, unit `U-A1`).
For every real order `s` and all `ξ η`,

`(1+‖ξ‖²)^{s/2} ≤ 2^{|s|/2} · (1+‖η‖²)^{s/2} · (1+‖ξ-η‖²)^{|s|/2}`.

The constant `2^{|s|/2}` is `peetreConst s`. Both signs of `s` are covered:
`s ≥ 0` raises the base bound directly, and `s < 0` applies it to the swapped
pair `(η, ξ)` at order `-s` and inverts. -/
theorem weight_ratio_le (s : ℝ) (ξ η : Space) :
    (1 + ‖ξ‖ ^ 2) ^ (s / 2) ≤
      2 ^ (|s| / 2) * (1 + ‖η‖ ^ 2) ^ (s / 2) * (1 + ‖ξ - η‖ ^ 2) ^ (|s| / 2) := by
  rcases le_or_gt 0 s with hs | hs
  · -- `s ≥ 0`: `|s| = s`, raise the base bound directly.
    rw [abs_of_nonneg hs]
    exact rpow_base_le hs ξ η
  · -- `s < 0`: apply the base raise to the swapped pair `(η, ξ)` at order `-s`.
    have hsnn : (0 : ℝ) ≤ -s := by linarith
    have hswap := rpow_base_le hsnn η ξ
    rw [norm_sub_rev η ξ] at hswap
    -- `hswap : (1+‖η‖²)^{-s/2} ≤ 2^{-s/2} (1+‖ξ‖²)^{-s/2} (1+‖ξ-η‖²)^{-s/2}`.
    rw [abs_of_neg hs]
    -- The negative-order powers are reciprocals of the positive-order ones.
    have hcx : (1 + ‖ξ‖ ^ 2) ^ (s / 2) * (1 + ‖ξ‖ ^ 2) ^ (-s / 2) = 1 := by
      rw [← Real.rpow_add (by positivity), show s / 2 + -s / 2 = 0 by ring,
        Real.rpow_zero]
    have hcy : (1 + ‖η‖ ^ 2) ^ (s / 2) * (1 + ‖η‖ ^ 2) ^ (-s / 2) = 1 := by
      rw [← Real.rpow_add (by positivity), show s / 2 + -s / 2 = 0 by ring,
        Real.rpow_zero]
    have hpos :
        (0 : ℝ) < (1 + ‖ξ‖ ^ 2) ^ (-s / 2) * (1 + ‖η‖ ^ 2) ^ (-s / 2) := by positivity
    -- Multiply the goal through by the positive quantity `(1+‖ξ‖²)^{-s/2}(1+‖η‖²)^{-s/2}`.
    refine le_of_mul_le_mul_right ?_ hpos
    calc
      (1 + ‖ξ‖ ^ 2) ^ (s / 2)
            * ((1 + ‖ξ‖ ^ 2) ^ (-s / 2) * (1 + ‖η‖ ^ 2) ^ (-s / 2))
          = ((1 + ‖ξ‖ ^ 2) ^ (s / 2) * (1 + ‖ξ‖ ^ 2) ^ (-s / 2))
              * (1 + ‖η‖ ^ 2) ^ (-s / 2) := by ring
      _ = (1 + ‖η‖ ^ 2) ^ (-s / 2) := by rw [hcx, one_mul]
      _ ≤ 2 ^ (-s / 2) * (1 + ‖ξ‖ ^ 2) ^ (-s / 2) * (1 + ‖ξ - η‖ ^ 2) ^ (-s / 2) :=
            hswap
      _ = (2 ^ (-s / 2) * (1 + ‖η‖ ^ 2) ^ (s / 2) * (1 + ‖ξ - η‖ ^ 2) ^ (-s / 2))
            * ((1 + ‖ξ‖ ^ 2) ^ (-s / 2) * (1 + ‖η‖ ^ 2) ^ (-s / 2)) := by
          rw [show (2 ^ (-s / 2) * (1 + ‖η‖ ^ 2) ^ (s / 2) * (1 + ‖ξ - η‖ ^ 2) ^ (-s / 2))
                  * ((1 + ‖ξ‖ ^ 2) ^ (-s / 2) * (1 + ‖η‖ ^ 2) ^ (-s / 2))
                = 2 ^ (-s / 2) * (1 + ‖ξ‖ ^ 2) ^ (-s / 2) * (1 + ‖ξ - η‖ ^ 2) ^ (-s / 2)
                  * ((1 + ‖η‖ ^ 2) ^ (s / 2) * (1 + ‖η‖ ^ 2) ^ (-s / 2)) from by ring,
            hcy, mul_one]

/-- The same bound phrased with the explicit constant `peetreConst s`. -/
theorem weight_ratio_le_const (s : ℝ) (ξ η : Space) :
    (1 + ‖ξ‖ ^ 2) ^ (s / 2) ≤
      peetreConst s * (1 + ‖η‖ ^ 2) ^ (s / 2) * (1 + ‖ξ - η‖ ^ 2) ^ (|s| / 2) := by
  unfold peetreConst
  exact weight_ratio_le s ξ η

/-- The datum-layer weight `sobolevBesselWeight s ξ = ((1+‖ξ‖²)^{s/2} : ℝ)`
(`Paper3/SobolevHilbertModel.lean:24`) has real magnitude exactly the
inhomogeneous Sobolev weight `(1+‖ξ‖²)^{s/2}`. -/
theorem sobolevBesselWeight_norm (s : ℝ) (ξ : Space) :
    ‖sobolevBesselWeight s ξ‖ = (1 + ‖ξ‖ ^ 2) ^ (s / 2) := by
  rw [sobolevBesselWeight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]

/-- Peetre's weight-ratio inequality in the exact `sobolevBesselWeight`
spelling of the datum layer (unit `U-A3` consumes this directly). -/
theorem sobolevBesselWeight_norm_ratio_le (s : ℝ) (ξ η : Space) :
    ‖sobolevBesselWeight s ξ‖ ≤
      2 ^ (|s| / 2) * ‖sobolevBesselWeight s η‖ *
        ‖sobolevBesselWeight |s| (ξ - η)‖ := by
  -- Each magnitude unfolds to the real weight; the last factor uses order `|s|`,
  -- so its exponent is `|s| / 2` — exactly the target's last factor.
  simp only [sobolevBesselWeight_norm]
  exact weight_ratio_le s ξ η

end NSFormalization.Section3.T22
