# Lane 458-T15-U14-force-convergence — T15 U14: `forceConvergence` (the rescaled force tends to `0` in `L^q_t H^s_x` below the critical order, `q ∈ {1,2}`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/458-T15-U14-force-convergence` (git branch `erenup/458-T15-U14-force-convergence`, = lane 456's branch + `origin/erenup/integration-section3`:
lane 456's `Section3/T15/SobolevBound.lean` (`sobolevConst f s = 1 + Σᵢ C₀ᵢ^{1−s}(2πC₁ᵢ)^s`, `forceSobolev_memLp`, `packetSobolevBound : forceSobolevENormT 1 s F_ε ≤ ofReal (sobolevConst f s · (ε^{1/2} + ε^{1/2−s}))`
for `0 ≤ s ≤ 1`), lane 439's `Mixed.lean` (`mixed_memLp`, `packetMixedScaling` — the `s = 0` mixed base for `q = 2`: `mixedLebesgueENormT 2 2 F_ε = ofReal (ε^{α(2,2)})·‖F‖`, and how `forceSobolevENormT 2 0`
relates to `mixedLebesgueENormT 2 2` — check `Section3/T10`/T11 for the order-0 identity), lane 438's `Section3/T17/Sobolev.lean` (`norm_datum_mono`: datum norm monotone in the order;
`force_coefficient_path_real`), lane 428's `Section3/T20/YBound.lean` (`critLower`: order-lowering contraction on `PeriodicSobolev`), the registered `criticalOrder` (`Contracts/V1/Data.lean:259` and its
canonical copy — grep `criticalOrder` in `Section3/T10`; `criticalOrder 1 = 1/2`, `criticalOrder 2 = −1/2`), and `Paper1/ScalingLimits.lean:11 sobolev_error_tendsto_zero` (the real-power limit
`ε^{a} → 0` for `a > 0` packaged for these bounds). Read `CLAUDE.md`, **`research/T15/T15_SPLIT.md` §0 and unit U14** (`:231-238`), the canonical field `forceConvergence` (`Section3/T15/Scaling.lean:447-452`:
`∀ q, (q = 1 ∨ q = 2) → ∀ s < criticalOrder q.toReal, Tendsto (fun ε ↦ forceSobolevENormT q s (periodizedScaledForce f place.x₀ place.T ε)) (𝓝[>] 0) (𝓝 0)`), `paper/sections/03-torus.tex:133-158`, the
Section 4 analogue `Contracts/V1/Scaling.lean:427 forceConvergence` and its canonical proof in `Section4/I03/` (grep `forceConvergence`), `research/T15/REPORT_{439,456}.md`, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`. Build the closure you need first.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub; a stub is rejected outright.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line. Record every failed approach with its exact error text in the ATTEMPTS file.

## Goal
New module `formalization/NSFormalization/Section3/T15/Convergence.lean` (namespace `NSFormalization.Section3.T15`): `theorem forceConvergence` with type literally the `ScalingAPI` field over the raw
packet clauses actually needed + `place : PlacementData …` (probe by `exact`). Route: (i) `q = 1`, `0 ≤ s < 1/2`: `packetSobolevBound` gives `≤ ofReal (C_s(ε^{1/2} + ε^{1/2−s}))` with both exponents
positive, so the bound `→ 0` (`sobolev_error_tendsto_zero` or `Real.rpow` continuity + `ENNReal.tendsto_ofReal`), and `Tendsto` by squeeze (`tendsto_of_tendsto_of_tendsto_of_le_of_le` with the
`0 ≤ ·` lower bound); note the field quantifies `ε` over `𝓝[>] 0` while the bound holds on `Ioc 0 place.ε₀` — use `Filter.Eventually` on `𝓝[>] 0` (`Ioc_mem_nhdsGT`); (ii) `q = 1`, `s < 0`: negative-order
monotonicity `forceSobolevENormT 1 s ≤ forceSobolevENormT 1 0` (a path at order 0 is a path at order `s < 0` after the order-lowering map: `norm_datum_mono`/`critLower`-type contraction, applied
pathwise; the T18 lane 445 needs the same lemma — grep `Section3/T18/SobolevRate.lean` if it landed on this base and reuse) and (i) at `s = 0`; (iii) `q = 2`, `s < −1/2`: `forceSobolevENormT 2 s ≤
forceSobolevENormT 2 0` by the same monotonicity, and `forceSobolevENormT 2 0 F_ε = mixedLebesgueENormT 2 2 F_ε` (or `≤`; the order-0 Parseval identity per slice, `T15.periodicSobolevENorm_zero_eq` /
lane 363's `ParsevalZero.lean`) `= ofReal (ε^{α(2,2)})·‖F‖ → 0` since `α(2,2) = -3 + 3/2 + 1 = 1/2 > 0` (registered `alpha`). Deliverables: the module, `research/T15/probes/convergence_closes.lean`
(field by `exact` + the nonzero packet instance), `research/T15/axioms_u14.lean`, `research/T15/ATTEMPTS_U14.md`, U14 status line in `T15_SPLIT.md`. If one branch genuinely lacks an in-tree bridge,
deliver the others and record the exact residual.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T15.Convergence` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorem with exact statement / files / gaps with error text / commands and results). Also write it to `research/T15/REPORT_458.md`.
