# Lane 386-T22-UA1-weight-ratio — T22 U-A1: Peetre's weight-ratio inequality `(1+‖ξ‖²)^(s/2) ≤ 2^(|s|/2) (1+‖η‖²)^(s/2) (1+‖ξ−η‖²)^(|s|/2)`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/386-T22-UA1-weight-ratio` (git branch `erenup/386-T22-UA1-weight-ratio`, based on `origin/erenup/integration-section3`).
Read `CLAUDE.md`, **`research/T22/T22_SPLIT.md` §0 and unit U-A1 (and U-A3 for how it is consumed: the `cutoffMultiplier` field of `research/T22/Spec.lean`)**, the Section 4 D01
weight spellings (`Section4/D01/*.lean`: the inhomogeneous Sobolev weight `(1+‖ξ‖²)^(s/2)` — grep `sobolevWeight`/`weight` to match the exact function the datum layer uses, so U-A3 can
apply this lemma without conversion), `Section3/T12/TameProduct.lean` (lane 342's `torusWeightPeetre`, the lattice Peetre inequality — same shape on ℤ³; reuse its proof pattern), and
the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging** (hard analytic unit). An honest partial with the exact residual statement and error text beats a stub.
- Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`.

## Goal
New module `formalization/NSFormalization/Section3/T22/WeightRatio.lean` (namespace `NSFormalization.Section3.T22`): `theorem weight_ratio_le (s : ℝ) (ξ η : Space) :
(1 + ‖ξ‖^2) ^ (s/2) ≤ 2 ^ (|s|/2) * (1 + ‖η‖^2) ^ (s/2) * (1 + ‖ξ - η‖^2) ^ (|s|/2)` (in the exact weight spelling D01 uses; if D01's weight is a named `def`, state the lemma for it and
also the unfolded form), with `def peetreConst (s : ℝ) : ℝ := 2 ^ (|s|/2)` and `peetreConst_pos`. Route: Peetre — `1 + ‖ξ‖² ≤ 2 (1 + ‖η‖²)(1 + ‖ξ − η‖²)` (from `‖ξ‖ ≤ ‖η‖ + ‖ξ − η‖` and
`(a+b)² ≤ 2(a²+b²)`), then `Real.rpow` monotonicity for `s ≥ 0` (`Real.rpow_le_rpow`, `Real.mul_rpow`) and, for `s < 0`, apply the `s ≥ 0` case with `ξ, η` swapped and exponent `−s`, then
invert (`Real.rpow_neg`, `inv_le_inv`). Also the `ℝ≥0∞`/`ofReal` form if D01's weights live in `ℝ≥0∞` (check and provide whichever U-A3 needs, say which).

## Deliverables
1. `Section3/T22/WeightRatio.lean`; 2. probe `research/T22/probes/weight_ratio_closes.lean` (numeric instances `s = 1/2`, `s = −1`, and the D01-spelled form); 3. `research/T22/ATTEMPTS_UA1.md`,
`research/T22/axioms_ua1.lean`, status in `research/T22/T22_SPLIT.md` U-A1, report `research/T22/REPORT_386.md` (if a guard blocks the write, put the full report in your final message).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T22.WeightRatio` (0 errors), `lake env lean` on module / probe / axioms file; `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with exact error text / commands and results).
