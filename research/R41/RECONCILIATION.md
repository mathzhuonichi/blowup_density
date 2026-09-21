# R41 (thm:Rmain, Theorem 4.1) — reconciliation of the double-blind drafts A (lane 236, gpt-5.6-sol) and B (lane 237, gpt-6-astra) against the earlier skeleton `research/section4/STATEMENTS.md` §1(iv)

Lead: erenup, 2026-09-17 (UTC 00:20). Drafts: `.claude/worktrees/236-SPEC-r41-draft-a/research/R41/DraftA.lean`, `.claude/worktrees/237-SPEC-r41-draft-b/research/R41/DraftB.lean`.

## 1. Agreement (paper `04-whole-space.tex:7-14`)
Both drafts (independently, neither saw the skeleton) produce exactly four fields: (i) fixed-initial-velocity density for `a ∈ X_R`, `q ∈ {1,2}`, `s < s_q`; (ii) the zero-initial-velocity
**iff** as one biconditional field; the threshold-value sentence (`s_1 = 1/2`, `s_2 = −1/2`); and the regular-reference rider as **one family** `(g_ε, u_ε)` with `g_ε ∈ F_R`, same initial
velocity, lifespan **exactly** `T`, same earlier history on `[0, T − 2ε²]`, `‖g_ε − g‖_{L^qH^s} → 0`, `‖u_ε − v‖_{E_T} → 0`. Vocabulary: `BreakdownDenseR`, `RelativelyDense`, `breakdownSetRZero`,
`criticalOrder` (A) / literal `2/q − 3/2` (B), `maximalLifespanR`, `energyENorm`, `ClassicalSolutionR` — all registered.

## 2. Differences and rulings
| point | A | B | skeleton (STATEMENTS §1(iv)) | ruling |
|---|---|---|---|---|
| `q` | `q : ℕ`, cast `(q : ℝ≥0∞)` | `q : ℝ`, `ENNReal.ofReal q` | `q : ℝ` structure field with `hq` | **`q : ℝ≥0∞`, `(q = 1 ∨ q = 2)`, threshold `criticalOrder q.toReal`** (the convention fixed for R45/R46/R47; matches registered `forceConvergence`). |
| parameters `ν, T` | ∀-quantified in every field | same | fixed as structure fields | **∀-quantified** (both drafts; a fixed-parameter record is derivable). |
| (ii) | one `↔` field | one `↔` field | `densityZero` + `nonDensityZero` (two fields) | **one `↔` field** `zeroInitialDensityIff`. Lane 232's `RMainNonDensity.nonDensityZero` (skeleton shape) and lane 235's `breakdownDenseR_zero_of_subcritical` together give the `↔`; the registration lane proves the bridge. |
| threshold values | `criticalOrder 1 = 1/2 ∧ criticalOrder 2 = −1/2` | literal arithmetic | absent (delegated to `ThresholdAPI.energy`) | **keep** as A's field `thresholdValues` (the theorem states it; trivial to prove). |
| rider packaging | a `Type`-valued structure `RegularReferenceApproximation …` returned by the field, over a `RegularReferenceR` record (`RegularThrough` + `δ` + solution) | inline `Prop`: `∀ δ > 0, ∀ v : ClassicalSolutionR ν a g (T+δ), ∃ ε₀ > 0, 2ε₀² < T, ∃ f u, (∀ ε ∈ Ioo 0 ε₀, MemForceR (f ε) ∧ lifespan = T ∧ ∃ U : ClassicalSolutionR ν a (f ε) T, U.velocity = u ε ∧ history on [0, T−2ε²]) ∧ Tendsto (force diff) ∧ Tendsto (energy diff)` | `∀ ρ > 0, ∃ f u p ε …` with `IsMaximalSolution`, `limsupLeft = ⊤` | **B's inline `Prop`** (a contract field must be a `Prop`; A's record is fine as a research package). Drop B's `2ε₀² < T` (not in the paper; the history window is vacuous for `ε` with `T − 2ε² < 0`, harmless). `Tendsto` along `𝓝[>] 0` (B) rather than A's ε–η form. The skeleton's `limsupLeft = ⊤` conjunct is Theorem 4.2's `blowup` clause — not restated (same ruling as R45); exact lifespan is the rider's "singularity exactly at `T`". |
| reference hypothesis | `RegularReferenceR` record (`RegularThrough` + explicit margin + solution) | explicit `δ > 0`, `v : ClassicalSolutionR ν a g (T+δ)` | `RegularThrough ν a g T` | **B** (explicit `δ`, `v`), as in R45/R46/R47. |
| rider's `s`-hypothesis | `s < criticalOrder q` | `s < 2/q − 3/2` | `s < exponent q 0` | keep (`criticalOrder q.toReal`); both drafts note the paper's final sentence does not restate it — the reconciliation keeps it (the force convergence is in `L^qH^s`, which needs `s < s_q`). |

## 3. Decisions
Fields (names from B, conventions above): `fixedInitialDensity`, `zeroInitialDensityIff`, `thresholdValues`, `regularReferenceApproximation`. Namespace/structure name `RMainAPI`.
Docstrings: merge A's (more precise line citations `:8-11,13,32-42`) into B's.

## 4. Proof status (all on `erenup/integration`)
- `fixedInitialDensity`: lane 235 `Bindings.breakdownDenseR_of_subcritical` (exact shape modulo the `q` convention).
- `zeroInitialDensityIff`: `←` lane 235 `breakdownDenseR_zero_of_subcritical`; `→` lane 232 `not_breakdownDenseR_zero_of_q` (contrapositive at `s ≥ s_q`).
- `thresholdValues`: arithmetic.
- `regularReferenceApproximation`: lane 233 `insertionLifespanV2_of_data` + R42 record fields (`history`, `forceConvergence`, `energyRate`/`E_T` convergence — check the registered `energyRate`
  gives `energyENorm T (u_ε − v) → 0`; if only the rate estimate is registered, derive the limit), `memForceR_force`, `lifespan`, `solution`.
So the registration lane can bind all four fields; no new analysis is expected.

## 5. Next
Lane 248: reconciled `research/R41/Spec.lean` + merged `COMPARISON.md` (+ provenance copies). Then lane 249: register `R41.main_thresholds` V1 (32nd contract) with bindings from
232/233/235 and tests; `RMainNonDensity`/skeleton bridge noted in `COMPARISON.md`.
