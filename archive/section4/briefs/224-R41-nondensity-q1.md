# Lane 224-R41-nondensity-q1 — Theorem 4.1 (ii), the `q = 1` non-density clause: for `s ≥ s₁ = 1/2`, `B^R_{ν,0,T}` is not relatively dense in `F_R` for `L¹_t H^s` (from lane 223's R43 endpoint)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/224-R41-nondensity-q1` (git branch `erenup/224-R41-nondensity-q1`, based on lane 223's branch `erenup/223-R43-endpoint` = `origin/erenup/integration`
+ `Section4/R43/Endpoint.lean` (`inhomogeneousAtZero_of_memForceR : ∀ ν, 0 < ν → ∀ f, MemForceR f → forceSobolevENormL1 (1/2) f < ENNReal.ofReal (criticalConst * ν) → maximalLifespanR ν (fun _ => 0) f = ⊤`,
`criticalConst`, `criticalConst_pos`)). Read that module and `research/R43/REPORT_223.md`, then the R41 vocabulary in the owner's `verification/Contracts/V1/Data.lean:660-712`
(`breakdownSetIn`, `breakdownSetR ν a T = {f ∈ F_R : maximalLifespanR ν a f ≤ ofReal T}`, `breakdownSetRZero`, `RelativelyDense q s Y S := ∀ g ∈ Y, ∀ r > 0, ∃ f ∈ S, forceSobolevENorm q s (f - g) < r`,
`BreakdownDenseR ν a T q s := RelativelyDense q s forceClassR (breakdownSetR ν a T)`), `verification/Contracts/V1/Thresholds.lean` (`ThresholdAPI.exponent`, `l1 : exponent 1 s = 1/2 - s`,
`energy : exponent 1 0 = 1/2` — the registered `R41.threshold_arithmetic`), `research/section4/STATEMENTS.md:120-170` (`RMainAPI.nonDensityZero : ∀ s, exponent q 0 ≤ s → ∃ ρ > 0, ∀ f ∈ B_R ν 0 T, ρ ≤ normLqHs q s f`
— centred at `0 ∈ F_R`; and the paragraph "From R43 (Prop. 4.3) exactly one consequence …"), `research/R41D/Spec.lean` and `COMPARISON.md` (how R41's drafts spell these), the paper
`04-whole-space.tex:8-12,176-181` (thm:Rmain (ii) and the non-density paragraph: "`H^s ↪ H^{1/2}` with norm at most one for `s ≥ 1/2` gives the same obstruction in each stronger metric"),
lane 221's `Section4/R43/ForcePath.lean` (`isHomogeneousPath_of_isSobolevPath` and the G2 infimum comparison — the **template** for the order-monotonicity you need), D01's `lowerVectorL s r`
(`Section4/D01/HalfOrder.lean:79-110`; `forceSobolevENormL1 (1/2) f ≠ ⊤` at `:179` shows the path-lowering pattern), `CLAUDE.md` (contract import rules: `formalization/` cannot import
`Contracts`; local restatements must be verbatim with the `Data.lean` line cited, so the binding lane can bridge by `rfl`), `collaboration/HANDOFF.md` §0 and §2 P10, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
  Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; non-vacuity `example`s.
- **Statement fidelity:** the theorem must be the exact `BreakdownDenseR`/`RelativelyDense` vocabulary of `Data.lean` (restated verbatim locally if no local restatement exists — grep
  `Section4/` first for `breakdownSetR`/`RelativelyDense`; if a local copy exists, import it, do not duplicate) and the threshold spelled as `1/2` with a comment citing `Thresholds.lean` `l1`/`energy`.
- **Satisfiability rule:** if one fact remains open, isolate it as ONE named hypothesis with the exact statement, satisfiable by nonzero forces.

## Goal
1. `forceSobolevENorm_mono_order : ∀ (q : ℝ≥0∞) (s s' : ℝ), s ≤ s' → ∀ f, forceSobolevENorm q s f ≤ forceSobolevENorm q s' f` (at least for `q = 1` and `1/2 ≤ s`): both sides are infima
   over datum paths (`Data.lean:225-236`; local restatement — grep where `forceSobolevENorm` is defined for `formalization/`, probably `Section4/D01/`), so map an order-`s'` admissible path
   to an order-`s` one through `lowerVectorL s' s` (continuous linear, norm-nonincreasing: `‖lowerVectorL s' s v‖ ≤ ‖v‖` — prove or locate), preserving measurability/`L^q` membership and
   the `IsSobolevPath` clauses (221's `isHomogeneousPath_of_isSobolevPath` did exactly this for the homogeneous conversion).
2. `nonDensityZero_L1 : ∀ ν T : ℝ, 0 < ν → 0 < T → ∀ s : ℝ, 1/2 ≤ s → ∃ ρ : ℝ, 0 < ρ ∧ ∀ f ∈ breakdownSetRZero ν T, ENNReal.ofReal ρ ≤ forceSobolevENorm 1 s f` with `ρ = criticalConst * ν`
   (contrapositive of `inhomogeneousAtZero_of_memForceR`: `f ∈ breakdownSetRZero` ⇒ `maximalLifespanR ν 0 f ≤ ofReal T < ⊤` ⇒ `¬ (forceSobolevENormL1 (1/2) f < ofReal (c ν))` ⇒ then item 1).
3. `not_breakdownDenseR_zero_L1 : ∀ ν T, 0 < ν → 0 < T → ∀ s, 1/2 ≤ s → ¬ BreakdownDenseR ν (fun _ => 0) T 1 s` (take `g = 0 ∈ forceClassR`, `r = ofReal ρ`, note `f - 0 = f`).
   Also state the same with the threshold written through a `ThresholdAPI`-shaped local `exponent` if `research/R41D/Spec.lean` does so (say which).
4. Non-vacuity: `0 ∈ forceClassR`; and an `example` that the hypotheses are satisfiable (`ν = T = 1`, `s = 1/2`).

## Deliverables
1. New module `formalization/NSFormalization/Section4/R41/NonDensityL1.lean` (namespace `NSFormalization.Section4.R41`; create the directory).
2. Records `research/R41D/ATTEMPTS_NONDENSITY_L1.md` (or `research/R41/` — create it), update `research/R41D/COMPARISON.md` (which `RMainAPI` field is now proved at `q = 1`), conformance
   `research/R41D/axioms_nondensity_l1.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.R41.NonDensityL1` (silent), `lake env lean` on the module (0 output), the axioms file, `make check`.

## Report
Commit on your branch; end with four parts. Also write it to `research/R41D/REPORT_224.md`.
