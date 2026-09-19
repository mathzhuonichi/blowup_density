# Lane 465-T19-U13-U14-closure — T19 wave 3: `simultaneousPairConvergence` (U13) and `closureInEnergy` (U14)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/465-T19-U13-U14-closure` (git branch `erenup/465-T19-U13-U14-closure`, = `origin/erenup/integration-section3` after lanes 461 (T19 U0) and 464 (U7–U9) merged).
Read `CLAUDE.md`, **`research/T19/T19_SPLIT.md`** (§0; wave 3 units U13/U14 verbatim targets and routes), `research/T19/REPORT_461.md` + `Section3/T19/Threading.lean` (`extendByZero`, `extendByZero_velocity_eqOn`, `insertionData`, `insertion`,
export lemmas `force_mem`, `lifespan`, `solution`, `blowup_limsup`, `energyRate`, `forceDifference_sobolev_bound`, `forceDifference_negativeSobolev_tendsto`, guards, `exists_force_close` — verify names by `grep -n`), `research/T19/REPORT_464.md` +
`Section3/T19/DensityEngine.lean` (how U7 turned the T18 bounds into "eventually `< r`"), `Section3/T19/Density.lean` (`StrongClosureAPI.simultaneousPairConvergence`, `.closureInEnergy` — read the exact statements; `RegularTrajectoryT`/`SingularTrajectoryT`
definitions in `research/T19/Spec.lean:138-159` and their canonical copies), `Section3/T19/Bookkeeping.lean` (`referenceFiniteEnergy` U5, `energyTimeEmbedding` U4), the T11 uniqueness used for the R41 `href` step
(`Bindings/MainThresholds.lean:104-124`; torus: `velocity_unique`/`PeriodicLocalTheoryAPI` in `Section3/T11/Assembly.lean` — grep), the R³ template `Bindings/CompletedClosure.lean:122 strongTrajectoryClosure_of_realization`, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`. Build the closure first
  (`lake build NSFormalization.Section3.T19.DensityEngine`).
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub; a stub is rejected outright.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line. Record every failed approach with its exact error text in the ATTEMPTS file.

## Goal
New module `formalization/NSFormalization/Section3/T19/Closure.lean` (namespace `NSFormalization.Section3.T19`):
1. **U13 `simultaneousPairConvergence`** with the canonical field's type (probe by `exact`). Route: from the given reference `w : ClassicalSolutionT ν a g (T+δ)` build `ins := insertion … (extendByZero w)` (U0); per `ε ∈ Ioc 0 ε₀`: `f ε := ins.force ε`
   (`force_mem`, `lifespan` gives `maximalLifespanT ν a (f ε) = ofReal T`, `solution` gives the classical solution `w_ε` with `w_ε.velocity = ins.velocity ε`); `SingularTrajectoryT ν a T (u ε)` from finite `E_T` (U5 `referenceFiniteEnergy` at the
   reference + `energyRate` triangle inequality for `energyENormT`) and blow-up (`blowup_limsup`); the `energyENormT`-limit of `u ε − w.velocity`: `energyRate` bounds `energyENormT T (u ε − (extendByZero w).velocity)`, and `energyENormT T` only sees
   `[0,T) ⊆ Ico 0 (T+δ)` where `(extendByZero w).velocity = w.velocity` (`extendByZero_velocity_eqOn`; if `energyENormT` is not manifestly restricted to `[0,T)`, prove the congruence lemma `energyENormT_congr_Ico`), constants `→ 0` along `𝓝[>] 0`
   (`ε^{1/2}`, `ε^{3/2}` powers as in `DensityEngine.lean`); the `∀ s < 1/2` `L¹_tH^s_x` limit exactly as U7's eventual-`< r` step but as a `Tendsto` (`forceDifference_sobolev_bound` for `0 ≤ s < 1/2`, `forceDifference_negativeSobolev_tendsto` for `s < 0`).
   Read the exact field: it may quantify the family as `∃ u f : ℝ → …, ∀ ε ∈ Ioc 0 ε₀, …` with `ε₀` existential — match token-for-token.
2. **U14 `closureInEnergy`**: unpack `RegularTrajectoryT ν a T u` to `g ∈ 𝓕`, `δ > 0`, `w` with `w.velocity = u`; apply U13; from the `energyENormT` `Tendsto` extract `ε` with the distance `< r` (`(tendsto_order.1 h).2 _ hr` / `Filter.Eventually.exists`
   with `Ioc_mem_nhdsGT`), `u' := u ε`.
Deliverables: the module, `research/T19/probes/closure_closes.lean` (both fields by `exact`), `research/T19/axioms_u13_u14.lean`, `research/T19/ATTEMPTS_U13_U14.md`, status lines in `T19_SPLIT.md`. If U13 does not close in time, deliver its
closed clauses as separate theorems with the exact residual clause named (no partial structure passed off as the field).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T19.Closure` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with error text / commands and results). Also write it to `research/T19/REPORT_465.md`.
