import NSFormalization.Section3.T22.WeightRatio

/-!
Probe for T22 unit U-A1 (`Section3/T22/WeightRatio.lean`).

Checks that `weight_ratio_le` closes at the numeric orders `s = 1/2` and
`s = -1` (positive and negative sign of the exponent), and that the
D01-spelled `sobolevBesselWeight` form applies verbatim.
-/

open NavierStokes.ProblemStatement (Space)
open NSFormalization.Section3.T22

-- Positive fractional order `s = 1/2`: the `|s| = s` branch.
example (ξ η : Space) :
    (1 + ‖ξ‖ ^ 2) ^ ((1 / 2 : ℝ) / 2) ≤
      2 ^ (|(1 / 2 : ℝ)| / 2) * (1 + ‖η‖ ^ 2) ^ ((1 / 2 : ℝ) / 2) *
        (1 + ‖ξ - η‖ ^ 2) ^ (|(1 / 2 : ℝ)| / 2) :=
  weight_ratio_le (1 / 2) ξ η

-- Negative order `s = -1`: the reciprocal branch.
example (ξ η : Space) :
    (1 + ‖ξ‖ ^ 2) ^ ((-1 : ℝ) / 2) ≤
      2 ^ (|(-1 : ℝ)| / 2) * (1 + ‖η‖ ^ 2) ^ ((-1 : ℝ) / 2) *
        (1 + ‖ξ - η‖ ^ 2) ^ (|(-1 : ℝ)| / 2) :=
  weight_ratio_le (-1) ξ η

-- The `peetreConst` form and its positivity at both signs.
example (ξ η : Space) :
    (1 + ‖ξ‖ ^ 2) ^ ((-1 : ℝ) / 2) ≤
      peetreConst (-1) * (1 + ‖η‖ ^ 2) ^ ((-1 : ℝ) / 2) *
        (1 + ‖ξ - η‖ ^ 2) ^ (|(-1 : ℝ)| / 2) :=
  weight_ratio_le_const (-1) ξ η

example : (0 : ℝ) < peetreConst (1 / 2) := peetreConst_pos _
example : (0 : ℝ) < peetreConst (-1) := peetreConst_pos _

-- The exact datum-layer weight spelling used by U-A3 (`sobolevBesselWeight`).
example (ξ η : Space) :
    ‖NSFormalization.Paper3.sobolevBesselWeight (-1) ξ‖ ≤
      2 ^ (|(-1 : ℝ)| / 2) * ‖NSFormalization.Paper3.sobolevBesselWeight (-1) η‖ *
        ‖NSFormalization.Paper3.sobolevBesselWeight |(-1 : ℝ)| (ξ - η)‖ :=
  sobolevBesselWeight_norm_ratio_le (-1) ξ η

-- The magnitude bridge itself, at `s = 1/2`.
example (ξ : Space) :
    ‖NSFormalization.Paper3.sobolevBesselWeight (1 / 2) ξ‖ =
      (1 + ‖ξ‖ ^ 2) ^ ((1 / 2 : ℝ) / 2) :=
  sobolevBesselWeight_norm (1 / 2) ξ
