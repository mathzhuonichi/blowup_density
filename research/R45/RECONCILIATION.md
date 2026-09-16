# R45 (cor:Rclasses) — reconciliation of the double-blind drafts A (lane 238, gpt-5.6-sol) and B (lane 239, gpt-6-astra)

Lead: erenup, 2026-09-16 (UTC 23:10). Drafts: `.claude/worktrees/238-SPEC-r45-draft-a/research/R45/DraftA.lean` (7 fields, per class), `.claude/worktrees/239-SPEC-r45-draft-b/research/R45/DraftB.lean`
(4 fields, parametric in the ambient class `Y`).

## 1. Agreement (paper `04-whole-space.tex:194-215`)
Both drafts state, for `Y ∈ {F_c, F_rd}`: (a) density of `breakdownSetIn Y ν a T` in `Y` for every `a ∈ X_R`, `q ∈ {1,2}`, `s < s_q`; (b) the zero-datum `iff`; (c) the Schwartz-datum
specialization for `F_rd` (`:195,198`); (d) the regular-reference rider with approximants **staying in `Y`**, exact lifespan `T`, same earlier history, `E_T` and `L^qH^s` closeness.
A splits (a),(b),(d) per class (`compact*`, `rapid*`); B is parametric with `(Y = forceClassCompact ∨ Y = forceClassRapid)`. A uses `q : ℕ`, B `q : ℝ`. A bundles the rider in
`HasReferenceApproximationRider Y ν T q s a g δ v` (`∀ tolerances, history cutoff, ∃ f u …`); B writes it inline (`∀ τ < T, ∀ r η > 0, ∃ f ∈ Y, ∃ u : ClassicalSolutionR ν a f T, lifespan = T ∧
‖f−g‖ < r ∧ ‖u−v‖_{E_T} < η ∧ history on [0,τ] ∧ unbounded speed near T`).

## 2. Decisions
1. **Parametric `Y`** (B): one field each for (a), (b), (d) with the hypothesis `Y = forceClassCompact ∨ Y = forceClassRapid`; (c) as its own field (`schwartzDensity`) for `F_rd`. Rationale:
   `breakdownSetIn`/`RelativelyDense` are already parametric in `Y` (`Data.lean:672,700`) and the manuscript states the corollary once for both classes.
2. **`q : ℝ≥0∞`, `(q = 1 ∨ q = 2)`, threshold `criticalOrder q.toReal`** — the shared convention (R41/R46 reconciliations); neither draft's cast (`(q : ℝ≥0∞)` from `ℕ`, `ENNReal.ofReal q` from `ℝ`) is kept.
3. **Rider (d): B's inline ε-form**, minus the last conjunct (unbounded speed near `T`: the corollary's text does not restate it; it is Theorem 4.2's `blowup` clause and belongs to the R42
   contract), and with `a ∈ initialClassR` only (B's `(a ∈ X_R ∨ a ∈ S_σ)` is redundant once G4 `initialClassSchwartz ⊆ initialClassR` is proved — lane 234). History window: B's arbitrary
   cutoff `τ < T` (matches Theorem 4.2's "arbitrarily long earlier history", `:36`), not A's `T − 2ε²`.
4. Field names: `density`, `zeroIff`, `schwartzDensity`, `regularReference` (B).

## 3. Proof dependencies
(a),(b): Theorem 4.1's arguments with `Y` replaced: the density branch needs the inserted forces to stay in `F_c`/`F_rd` (G3 rapid-class closure, lane 234; `F_c` closure from
`forceDifference_compact`), the non-density branch is inherited from `F_R` via `Y ⊆ F_R` (G2, lane 234) and `breakdownSetIn Y ⊆ breakdownSetR`. (c): G4 + (a). (d): lane 233's record + R42 fields.

## 4. Next
Registration lane after R41's (`Contracts/V1/ForceClasses.lean`, `RClassesAPI`, `research/R45/Spec.lean`, merged `COMPARISON.md`); then proof lanes per field.
