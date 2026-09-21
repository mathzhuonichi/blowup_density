# Lane 386 — T22 U-A1: Peetre's weight-ratio inequality (Opus prover; transcribed by the lead from the agent's final message — report-file guard)

Commit `40e1075d2807b065da07e77bab3b3e00aab70752` on `erenup/386-T22-UA1-weight-ratio`. No `sorry`/`axiom`/`native_decide`, no named input, no `maxHeartbeats` bump; every declaration `[propext, Classical.choice, Quot.sound]`.

## 1. What was proved (`Section3/T22/WeightRatio.lean`, namespace `NSFormalization.Section3.T22`)
- `peetreConst s := 2 ^ (|s|/2)`, `peetreConst_pos`.
- `one_add_normSq_le (ξ η) : 1 + ‖ξ‖² ≤ 2 (1 + ‖η‖²)(1 + ‖ξ − η‖²)`; `rpow_base_le (ht : 0 ≤ t)` — the nonnegative-order raise.
- **`weight_ratio_le (s) (ξ η) : (1 + ‖ξ‖²)^(s/2) ≤ 2^(|s|/2) · (1 + ‖η‖²)^(s/2) · (1 + ‖ξ − η‖²)^(|s|/2)`** (all real `s`; `s < 0` by applying the base raise to the swapped pair at order `−s` and clearing reciprocal factors), and `weight_ratio_le_const` with `peetreConst`.
- D01 spelling: `sobolevBesselWeight_norm (s ξ) : ‖sobolevBesselWeight s ξ‖ = (1 + ‖ξ‖²)^(s/2)` and `sobolevBesselWeight_norm_ratio_le`, where `sobolevBesselWeight = NSFormalization.Paper3.sobolevBesselWeight` (`Paper3/SobolevHilbertModel.lean:24`) — the weight the datum/norm layer uses, so U-A3 applies it without conversion.

## 2. Files
`formalization/NSFormalization/Section3/T22/WeightRatio.lean`; `research/T22/probes/weight_ratio_closes.lean` (`s = 1/2`, `s = −1`, `peetreConst` form, positivity, D01 form); `research/T22/axioms_ua1.lean` (7); `research/T22/ATTEMPTS_UA1.md`; U-A1 status in `research/T22/T22_SPLIT.md`.

## 3. Gaps
None for U-A1. Pin notes (in ATTEMPTS): `le_or_lt` → `le_or_gt`; `Complex.norm_ofReal` → `Complex.norm_real` + `Real.norm_eq_abs`; no bare `div_le_div_iff` / `Real.rpow_le_rpow_of_nonpos` at this pin (the `s < 0` case avoids division).

## 4. Commands and results
`lake build NSFormalization.Section3.T22.WeightRatio` → built, 0 errors; probe → exit 0; axioms → 7 × standard; `make check` → exit 0.
