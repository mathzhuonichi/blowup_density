# R47 (thm:Rgrid) — reconciliation of the double-blind drafts A (lane 240, gpt-5.6-sol) and B (lane 241, gpt-6-astra)

Lead: erenup, 2026-09-16 (UTC 23:40). Drafts: `.claude/worktrees/240-SPEC-r47-draft-a/research/R47/DraftA.lean`, `.claude/worktrees/241-SPEC-r47-draft-b/research/R47/DraftB.lean`.

## 1. Agreement (paper `04-whole-space.tex:297-304`)
Both: for every regular reference of Theorem 4.2 and every **finite family of complete uniform Cartesian grids** (registered `Data.Grid`, `Data.gridObservation`), ONE inserted family
`(g_ε, u_ε)` such that for every grid in the family and every `t ∈ [0,T)`: `A_h u_ε(t) = A_h v(t)` and `A_h g_ε(t) = A_h g(t)`; exact lifespan `T_max(a,g_ε) = T`; the `E_T` convergence and the
three-norm force convergence of Prop. 4.6; all differences (velocity, force, pressure modulo a time-dependent spatial constant) supported in one ball that lies in one cell of every grid.

## 2. Differences and rulings
| point | A | B | ruling |
|---|---|---|---|
| shape | a record `RGridAPI ν P ι grids` **about a given** `InsertionFamilyAPI` (`family` field) | an **existence** statement `choose : ∀ ν a g T δ reference n grids, Nonempty (RGridFamily …)` over raw data | **B** (the theorem asserts existence "the inserted solutions may be chosen so that"; matches R46's ruling and lane 233's constructor). A's per-field content is folded into `RGridFamily`. |
| grid family index | `ι : Type` `[Finite ι]` | `n : ℕ`, `Fin n → Grid` | **`Fin n`** (concrete; a `Finite ι` version is derivable). |
| ball ⊆ cell | `ball ⊆ (grids i).cell k` | `closure (ball) ⊆ interior (cell k)` | **A's plain containment** — the paper says "contained in a cell" (`:303-304`); B's strengthening is a proof convenience, not the statement. |
| `L¹_tL²_x` force norm | `Data.mixedLebesgueENorm 1 2` | `forceSobolevENorm 1 0` | **`forceSobolevENorm 1 0`** (the R46 reconciliation's choice; `H⁰ = L²` — the registration lane checks `mixedLebesgueENorm 1 2 = forceSobolevENorm 1 0` if the former is registered and notes it). |
| pressure gauge | `PressureDifferenceSupportedInBallModuloGauge` (local def, "needs registration") | inline `∃ c : ℝ → ℝ, ∀ t ∈ Ico 0 T, tsupport (… − c t) ⊆ ball` | **inline** (B); no new registered notion. |
| history | not stated (inherited from Theorem 4.2's record) | `∀ t ≤ T − 2ε²` pointwise equality with the reference | **keep B's field** (Theorem 4.7 is "under the hypotheses of Theorem 4.2" and the proof uses the same family; stating the inherited clause explicitly is what the R46 ruling also did). |
| solutions | via the record (`family.velocity`, lifespan field) | `solution : ∀ ε, ClassicalSolutionR ν a (force ε) T` + `lifespan` | **B** (explicit classical solutions; lifespan exact). |
| `RegularThrough` | via the record's `reference` | explicit `δ > 0` and `reference : ClassicalSolutionR ν a g (T+δ)` | **B** (same as R45/R46 rulings). |

## 3. Decisions
Structure `RGridFamily ν a g T δ reference n grids` with B's fields (`center`, `radius`, `radius_pos`, `containingCell` (plain `ball ⊆ cell`), `ε₀`, `eps_pos`, `force`, `solution`, `force_mem`,
`history`, `forceDifference_compact`, `velocity_observations`, `force_observations`, `lifespan`, `energy_convergence`, `force_convergence` (with `forceSobolevENorm 1 0`), `velocity_support`,
`pressure_support`, `force_support`) and `RGridAPI` with the single field `choose` (B). Docstrings: merge A's (paper-line citations are more precise on `:298-304`) into B's.

## 4. Proof dependencies
Lane 233's record + R42 fields (`history`, `velocityDifference_support`, `pressureDifference_support`, `forceDifference_ball`, `forceDifference_compact`, `energyRate`, `forceConvergence`) +
the grid-avoidance choice of the insertion ball (I02's `x₀, r` free parameters: choose the ball inside a common cell of finitely many grids — a new small lemma) + `gridObservation` locality
(observations of a field supported in a cell agree — needs `Data.gridObservation`'s definition; check `Data.lean` §"grid" for an existing locality lemma) + the `L²Ḣ⁻¹` convergence (open, I03).

## 5. Next
Registration-shaped `research/R47/Spec.lean` + merged `COMPARISON.md` (lane 246); proofs after R46's strong closure lands.
