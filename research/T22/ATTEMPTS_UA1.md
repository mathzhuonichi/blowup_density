# T22 U-A1 — Peetre weight-ratio: attempts and pitfalls (lane 386)

Target (`research/T22/T22_SPLIT.md` U-A1, `03-torus.tex:616-624`):
`(1+‖ξ‖²)^{s/2} ≤ 2^{|s|/2} (1+‖η‖²)^{s/2} (1+‖ξ-η‖²)^{|s|/2}` for all real `s`.
Delivered in `formalization/NSFormalization/Section3/T22/WeightRatio.lean`.

## Route that worked

1. `one_add_normSq_le` — base Peetre `1+‖ξ‖² ≤ 2(1+‖η‖²)(1+‖ξ-η‖²)`.
   Triangle `‖ξ‖ ≤ ‖η‖+‖ξ-η‖` (via `norm_add_le η (ξ-η)` after `abel`-cancel
   `η+(ξ-η)=ξ`), square it with `pow_le_pow_left₀`, then `nlinarith` with the
   SOS certificate `1 + (a-b)² + 2(ab)²` (`a=‖η‖`, `b=‖ξ-η‖`), passing
   `sq_nonneg (‖η‖-‖ξ-η‖)` and `sq_nonneg (‖η‖*‖ξ-η‖)` as hints.
2. `rpow_base_le {t} (ht : 0 ≤ t)` — raise (1) to `t/2 ≥ 0` by `Real.rpow_le_rpow`
   then split with two `Real.mul_rpow` rewrites. One helper serves both signs.
3. `weight_ratio_le` — case split on `sign s`:
   - `0 ≤ s`: `|s|=s`, `exact rpow_base_le hs ξ η`.
   - `s < 0`: `hswap := rpow_base_le (0 ≤ -s) η ξ` (swapped pair, order `-s`),
     `norm_sub_rev` to turn `‖η-ξ‖` into `‖ξ-η‖`. The two order-`s` powers are
     reciprocals of the order-`-s` ones (`(1+‖·‖²)^{s/2}·(1+‖·‖²)^{-s/2}=1` via
     `Real.rpow_add` + `Real.rpow_zero`), so multiply the goal through by the
     positive `(1+‖ξ‖²)^{-s/2}(1+‖η‖²)^{-s/2}` (`le_of_mul_le_mul_right`) and a
     `calc` reduces exactly to `hswap`.
4. Datum-layer bridge: `sobolevBesselWeight_norm` gives
   `‖sobolevBesselWeight s ξ‖ = (1+‖ξ‖²)^{s/2}`, hence
   `sobolevBesselWeight_norm_ratio_le` — the same bound in the exact spelling
   `NSFormalization.Paper3.sobolevBesselWeight` that the datum/norm layer uses,
   so U-A3 applies it with no conversion.

## Failed approaches / pin-specific name changes (v4.34.0-rc2 + Mathlib)

- `le_or_lt 0 s` → **`Unknown identifier`**. Renamed to `le_or_gt 0 s`
  (`0 ≤ s ∨ 0 > s`; the second disjunct is defeq `s < 0`, feeds `abs_of_neg`).
- `Complex.norm_ofReal` → **`Unknown constant`**. The available lemma is
  `Complex.norm_real (r : ℝ) : ‖(r:ℂ)‖ = ‖r‖`; finish with `Real.norm_eq_abs`
  then `abs_of_nonneg`.
- Bare `div_le_div_iff` does **not** exist at this pin (only `div_le_div_iff'`,
  `_left`, `_right`). Rather than chase the right variant, the negative-order
  case avoids division entirely via `le_of_mul_le_mul_right` + a `ring`/`calc`
  clearing of the reciprocal factors — fully deterministic, no `nlinarith` over
  inverses.
- `Real.rpow_le_rpow_of_nonpos` (antitone-in-base for a fixed nonpositive
  exponent) does **not** exist under that name; the swap-and-invert route above
  never needs it, so this dead end was abandoned before writing.

## Notes

- All `^` on `(1+‖·‖²)` and on `2` in the statement are `Real.rpow` (real
  exponent). `‖ξ‖^2` is the `ℕ`-power; kept as `‖ξ‖ ^ 2` to match the
  `sobolevBesselWeight` spelling character-for-character.
- No `maxHeartbeats` bump was needed (module builds in ~2.6s).
- No named input, no placeholder, no goal repackaging: the whole content is the
  concrete estimate, exactly as required for this hard analytic unit.
