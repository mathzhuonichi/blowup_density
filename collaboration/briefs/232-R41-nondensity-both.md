# Lane 232-R41-nondensity-both — Theorem 4.1(ii)'s non-density clause in the `RMainAPI` skeleton shape for `q ∈ {1, 2}`: `nonDensityZero` from lanes 224 (q = 1) and 229 (q = 2)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/232-R41-nondensity-both` (git branch `erenup/232-R41-nondensity-both`, based on lane 229's branch `erenup/229-R44-prop44` = `origin/erenup/integration`
+ `Section4/R41/NonDensityL2.lean` (`nonDensityZero_L2`, `not_breakdownDenseR_zero_L2`, `s ≥ -1/2`, `ρ = R44.radius ν T`) — with `Section4/R41/NonDensityL1.lean` (lane 224: `nonDensityZero_L1`,
`not_breakdownDenseR_zero_L1`, `s ≥ 1/2`, `ρ = R43.criticalConst·ν`; `forceSobolevENorm_mono_order`; the local restatements of `breakdownSetRZero`/`RelativelyDense`/`BreakdownDenseR`) on integration).
Read both modules, `research/R41D/REPORT_224.md`, `research/R44/REPORT_229.md`, `research/section4/STATEMENTS.md:120-170` (the `RMainAPI` skeleton: `q : ℝ`, `hq : q = 1 ∨ q = 2`,
`thresholds : ThresholdAPI`, `nonDensityZero : ∀ s : ℝ, thresholds.exponent q 0 ≤ s → ∃ ρ : ℝ, 0 < ρ ∧ ∀ f, f ∈ ⟪D01:B_R⟫ ν 0 T → ρ ≤ ⟪D01:normLqHs⟫ q s f` — note `q : ℝ` there vs
`forceSobolevENorm (q : ℝ≥0∞)` in `Data.lean`: decide the cast (`ENNReal.ofReal q` or a `q : ℝ≥0∞` with `q = 1 ∨ q = 2`) and say why, matching `research/R41D/Spec.lean` if it fixes one),
`verification/Contracts/V1/Thresholds.lean` (`ThresholdAPI`, `l1`, `l2`, `energy`; the registered `R41.threshold_arithmetic` binding — grep `Bindings/Thresholds*.lean` for the witness),
`research/R41D/Spec.lean`, `research/R41D/COMPARISON.md`, `collaboration/tasks/R41.md`, the paper `04-whole-space.tex:8-12,176-181`, `CLAUDE.md`, `collaboration/HANDOFF.md` §0 and §2 P10,
and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; no heartbeat overrides expected. No edits to existing modules; new files only. Every declaration must print exactly
  `[propext, Classical.choice, Quot.sound]`; non-vacuity `example`s (`ν = T = 1`, both `q`).
- **Statement fidelity:** the theorem must be the `RMainAPI.nonDensityZero` field shape from `STATEMENTS.md` with the threshold through a `ThresholdAPI` value (use the registered binding's
  witness or restate `exponent q s = 2/q - 3/2 - s` verbatim with a `rfl` bridge remark) — no re-cut of the ball/threshold.

## Goal
1. `theorem nonDensityZero_of_q (thr : ThresholdAPI-shaped local record or the registered exponent) : ∀ q, (q = 1 ∨ q = 2) → ∀ ν T, 0 < ν → 0 < T → ∀ s, exponent q 0 ≤ s → ∃ ρ > 0, ∀ f ∈ breakdownSetRZero ν T, ENNReal.ofReal ρ ≤ forceSobolevENorm q s f`
   — by cases on `q`, from `nonDensityZero_L1` (`exponent 1 0 = 1/2`) and `nonDensityZero_L2` (`exponent 2 0 = -1/2`), with the explicit `ρ` in each case.
2. `theorem not_breakdownDenseR_zero_of_q : ∀ q, (q = 1 ∨ q = 2) → … → ¬ BreakdownDenseR ν (fun _ => 0) T q s` for `exponent q 0 ≤ s` (thm:Rmain (ii), the "only if" half at `a = 0`).
3. A `structure RMainNonDensity` (or a `def` bundling `ν T q hq thresholds` + the proved field) mirroring the skeleton's binders, with an `example` instance — so the future R41 assembly can
   take it by `⟨…⟩`. Do not claim `densityFixedInitial`/`densityZero`/`regularReferenceRider`.

## Deliverables
1. New module `formalization/NSFormalization/Section4/R41/NonDensity.lean` (namespace `NSFormalization.Section4.R41`).
2. Records `research/R41D/ATTEMPTS_NONDENSITY.md`, update `research/R41D/COMPARISON.md` (the `nonDensityZero` field proved for both `q`), conformance `research/R41D/axioms_nondensity.lean`
   (with a `Contracts.V1.Data`/`Thresholds` vocabulary conformance theorem).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.R41.NonDensity` (silent), `lake env lean` on the module (0 output), the axioms file, `make check`.

## Report
Commit on your branch; end with four parts. Also write it to `research/R41D/REPORT_232.md`.
