# Lane 210-A01-horizon-uniform — the `horizon_lower_bound` field: a horizon uniform over Sobolev balls, and the honest status of the H¹ clause

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/210-A01-horizon-uniform` (git branch `erenup/210-A01-horizon-uniform`, based on `origin/erenup/integration`, which contains lane 207's
`TameAssembly.lean` (unconditional `hb_of_base''`, `constructor_of_base`), lane 193's `AprioriFamily.lean` (the base horizon `S₆` from the vendor's local existence:
`hasAprioriBound_base`, the radius `‖u₀‖₇ + 1`, the time budget `exists_positive_time_budget`), lane 188's `MildUniqueness.lean` (`exists_positive_time_budget ν 0 L 1 S`,
`kernelMass`, `ballLipschitz`), the vendor's Picard local existence (`vendor/NavierStokesAndEuler/Euler/QuadraticHeatLocal.lean` and neighbours: the horizon `S₆ = ε/2` chosen from two
positive-time Picard budgets, per lane 193's report), and lane 208 (`LocalSolution.lean`, running concurrently: `localHorizon`). Read `CLAUDE.md`, `collaboration/HANDOFF.md` §0 and §2 P7,
**`research/A01/Spec.lean:300-345`** (the field, copy token-for-token: `horizon_lower_bound : ∀ ν, 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ → ∃ δ > 0, ∀ a f, a ∈ initialClassR → MemForceR f →
sobolevENorm 1 a ≤ K → forceSobolevENormL1 1 f ≤ K → δ ≤ horizon ν a f` and its docstring: the manuscript asserts an **H¹**-uniform duration citing Tao 2013 Theorems 5.1(ii)/5.4(ii)),
`paper/sections/appendix-a-local-theory.tex:140-157`, `research/A01/REPORT_193.md` (what the vendor horizon depends on), `research/A01/REVIEW_207-A01-tame-assembly.md` §5, and the
top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
  Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`.
- **Fidelity rule (rule 2):** do NOT silently change the contract's order. Prove what the tree supports and state the H¹ clause's status honestly.

## Goal
1. **What the tree gives:** the base-order horizon is chosen from the vendor's Picard budget, which depends on the order-7 norm of the datum and the order-6 force path. Prove the
   uniform lower bound **at that order**: `theorem horizon_lower_bound_H7 : ∀ ν, 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ → ∃ δ > 0, ∀ a f, a ∈ initialClassR → MemForceR f → sobolevENorm 7 a ≤ K →
   forceSobolevENormL1 7 f ≤ K → δ ≤ localHorizon ν a f` (use lane 208's `localHorizon` if landed; else state it for the existential horizon `S` produced by `constructor_of_base` as
   `δ ≤ S`), by tracing `exists_positive_time_budget`/`kernelMass`/`ballLipschitz` monotonicity in the radius: a bound on the data norms gives a bound on the Lipschitz constant `L`, hence a
   budget `δ(ν, K)` chosen **before** the datum. State the exact monotonicity lemmas used.
2. **The H¹ clause:** the manuscript's field is H¹-uniform (Tao's H¹ local theory). Assess honestly whether it follows from the tree: (a) via the a-priori family (H¹ ball + Grönwall gives
   all-order bounds only *on a given horizon*, not a horizon from H¹ data — circular?), (b) via a genuine H¹ local existence (absent in the tree: vendor Picard needs order ≥ 6; HeliCorgi's
   R³ lifespan is in terms of H²/H³ data — check `vendor/HeliCorgi/Formal/R3QuantitativeLifespan.lean` and say at which order). If the H¹ clause is not provable from the tree, write
   `def HorizonLowerBoundH1 : Prop` token-for-token as the contract field and record in the report the two honest options for the lead/owner: (i) a lane implementing an H¹ (or H³)
   quantitative local theory, or (ii) a V2 re-cut of the field to the order the tree supports — with the argument that A04's restart (the only consumer, `research/A01/REVIEW.md` M5)
   works with any fixed order because Grönwall bounds every `H^m` norm up to `S` (`appendix-a-local-theory.tex:146-150`). Do **not** decide the re-cut yourself.
3. Non-vacuity: instantiate the H⁷ bound on zero data.

## Deliverables
1. New module `formalization/NSFormalization/Section4/A01/HorizonUniform.lean` (namespace `NSFormalization.Section4.A01`).
2. Records `research/A01/ATTEMPTS_HORIZON_UNIFORM.md`, `A3_SPLIT.md` row 210, conformance `research/A01/axioms_horizon_uniform.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.HorizonUniform` (silent), `lake env lean` on the module (0 output), the axioms file, `make check`.

## Report
Commit on your branch; end with four parts. Also write it to `research/A01/REPORT_210.md`.
