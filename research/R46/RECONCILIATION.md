# R46 (prop:Renergy) — reconciliation of the double-blind drafts A (lane 242, gpt-5.6-sol) and B (lane 243, gpt-6-astra)

Lead: erenup, 2026-09-16 (UTC 23:10). Drafts: `.claude/worktrees/242-SPEC-r46-draft-a/research/R46/DraftA.lean`, `.claude/worktrees/243-SPEC-r46-draft-b/research/R46/DraftB.lean`
(both elaborate; both will be copied into this directory by the registration lane).

## 1. Agreement (paper `04-whole-space.tex:218-229`)

| clause | A | B | verdict |
|---|---|---|---|
| density in `L^q(0,∞;H^s)`, `q ∈ {1,2}`, `s < s_q`, of `{f ∈ F_c : T_max(a,f) ≤ T}` | `completedSobolevDensity` via registered `CompletedDense q s` (`Data.lean:741`) | `sobolevDensity` via registered `CompletedDenseVia q s (IsSobolevPath s)` (`Data.lean:732`) | **same predicate** (A's abbreviation unfolds to B's; the registration lane must check `rfl`). Quantifier order `a, ν, T, q, s` identical. Threshold: A `criticalOrder q.toReal` (registered `Data.lean:259`), B `2/q.toReal − 3/2` — **use `criticalOrder q.toReal`** (registered, `ThresholdAPI.formula`-compatible). |
| density in `L²(0,∞;Ḣ⁻¹)` | `completedHomogeneousDensity` via `CompletedDenseHomogeneous 2 (-1)` (`Data.lean:746`) | `homogeneousDensity` via `CompletedDenseVia 2 (-1) (IsHomogeneousPath (-1))` | **same predicate** (check `rfl`). |
| strong trajectory closure ("for every reference in Theorem 4.2 one may simultaneously arrange … `E_T` and the sum of the three force norms → 0") | quantifies over a **scaling record** `S : ScalingAPI ν P` and a reference `R` compatible with `S.correction`; ∃ family `A` with `A.scaling = S ∧ A.a = a ∧ StrongTrajectoryClosure A` | quantifies over **raw data** `a ∈ X_R, ν, T, g ∈ F_R, δ, RegularThrough, R : ClassicalSolutionR ν a g (T+δ), x₀, r`; ∃ packet + family with the correction fields pinned to the data, plus explicit `MemForceR (force ε)`, `maximalLifespanR = ofReal T`, a classical solution `U` with `U.velocity = A.velocity ε`, and both limits | **adopt B's raw-data form** (it is what the manuscript quantifies over — "for every reference in Theorem 4.2" — and what lane 233's `insertionLifespanV2_of_data` constructs). Keep the two `Tendsto` conjuncts exactly as both drafts state them (`energyENorm T` on the velocity difference; the sum `forceSobolevENorm 1 0 + forceSobolevENorm 2 (-1) + forceHomogeneousENorm 2 (-1)` on the force difference). The lifespan/solution conjuncts are re-exports of `R42.insertion_lifespan_v2` (`lifespan`, `solution`) — keep them (the paper says "the inserted solutions", i.e. solutions with lifespan exactly `T`). |

## 2. Decisions
1. Field names: `completedSobolevDensity`, `completedHomogeneousDensity`, `strongTrajectoryClosure` (A's names, B's third field body).
2. `q : ℝ≥0∞` with `(q = 1 ∨ q = 2)` and threshold `criticalOrder q.toReal` — the convention of the registered `forceConvergence` (`InsertionFamily.lean:323`) and `CompletedDenseVia`; no `ENNReal.ofReal` casts.
3. B's ball parameters `x₀ : Space`, `r > 0` in the strong-closure field: **drop from the statement** (the manuscript's proposition does not mention the insertion ball; Theorem 4.2's record carries it internally). The registration lane states `∃ P A, A.a = a ∧ A.scaling.correction.T = T ∧ A.scaling.correction.g = g ∧ A.scaling.correction.v = R.velocity ∧ A.scaling.correction.π = R.pressure ∧ …` without pinning `x₀, r`.
4. `RegularThrough ν a g (T+δ)` **and** the explicit `R : ClassicalSolutionR ν a g (T+δ)`: keep only the explicit `R` (it implies the former); the paper's "reference regular through `T+δ`" is `R` itself.
5. Ambiguity noted by both: `IsSobolevPath`/`IsHomogeneousPath` realize every nonnegative time while Bochner equivalence is a.e. — inherited registered vocabulary; not a statement issue.

## 3. Proof dependencies (for the split, not this reconciliation)
- Density fields: Theorem 4.1's relative density in `F_c` (R45, via lane 235's `breakdownDenseR_of_subcritical` with `Y = F_c` — needs R45's class version) + B01's approximation of completed-space targets by smooth compact forces (`Contracts/V1/BochnerPartial.lean`; the homogeneous assembly is explicitly omitted by `HomogeneousPartial` — open).
- Strong closure: lane 233's record + `R42.insertion_family` fields `energyRate`, `forceConvergence` at `(1,0)`, `(2,−1)` + a homogeneous convergence at `(2,−1)` (the `L²Ḣ⁻¹` clause — `Scaling` omits the homogeneous scaled estimate; open, I03).

## 4. Next
Registration lane (SPEC → `Contracts/V1/CompletedDensity.lean` as `REnergyAPI` with the three fields above, docstrings from both drafts, `research/R46/Spec.lean` = the reconciled statement, `COMPARISON.md` merged from A/B) after R41's registration (shared conventions).

## Addendum (lead, 23:45Z)
`Data.lean:251` registers `mixedLebesgueENorm (q p) f` (the literal `L^q_t L^p_x` norm). For the `L¹_tL²_x` term of the three-norm sum, the registration lane should spell `mixedLebesgueENorm 1 2` (literal manuscript fidelity) and add `example : mixedLebesgueENorm 1 2 f = forceSobolevENorm 1 0 f` (or a lemma) if it holds definitionally/provably; otherwise keep both spellings documented and let the owner choose. Lanes 245/246 running with the earlier wording should note this in their COMPARISON "open questions".
