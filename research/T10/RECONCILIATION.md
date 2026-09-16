# T10 (periodic data layer, Section 3 stage S3-0) — reconciliation of the double-blind drafts A (lane 263, gpt-5.6-sol, 63 min) and B (lane 264, gpt-5.6-sol after two astra router deaths)

Lead: erenup, 2026-09-17 (UTC 21:45). Drafts: `.claude/worktrees/263-SPEC-t10-draft-a/research/T10/DraftA.lean`, `.claude/worktrees/264-SPEC-t10-draft-b/research/T10/DraftB.lean` (both elaborate; both copy Section 4's D01 "datum" architecture as instructed).

## 1. Agreement
Torus `UnitAddTorus (Fin 3)`, lattice `Fin 3 → ℤ`; physical layer = unit-periodic fields on `EuclideanSpace ℝ (Fin 3)`; `torusLift`/`periodicFourierCoeff` restated from `Paper1/TorusCube.lean` (unit-period character); Bessel weight **`(1 + 4π²|k|²)^{s/2}`** stored inside the datum; datum bridge `IsPeriodicDatum s z A` (coefficients of `z` = weighted `A`); `periodicSobolevENorm s z` = infimum over representing data (`⊤` if none); `meanT` via normalized Haar; mean-zero part; mean-zero coefficient subspace (`A(0) = 0`); periodic Leray projector on data (identity at `k = 0`, `I − k⊗k/|k|²` otherwise); pressure gauge `∫ p(t,·) = 0`; classes `initialClassT`/`forceClassT`; `ClassicalSolutionT`; `maximalLifespanT`; `breakdownSetT`; `RelativelyDenseT`; `energyENormT`.

## 2. Differences and rulings
| point | A | B | ruling |
|---|---|---|---|
| coefficient carrier | `lp (Fin 3 → ℤ) 2` of `EuclideanSpace ℂ (Fin 3)` (raw complex carrier; realness only inside `IsPeriodicDatum`) | `WithLp 2 (Fin 3 → lp ℂ 2)` **restricted to the real submodule** `A_i(−k) = conj (A_i k)` (`PeriodicSobolev s := realPeriodicSubmodule`, a real Hilbert space) | **B**: contracts quantify over the carrier (`∀ A : PeriodicSobolev s`), so it must be the real Hilbert space, exactly as Section 4's `RealVectorSobolev` (`Data.lean:150-260`). A's raw carrier admits non-real data. (The two are isometric on real data.) |
| realness | — | `realPeriodicSubmodule` | keep B; add the lemma "`IsPeriodicDatum` lands in the real submodule" to the needs-a-lemma list. |
| solenoidal / Leray | projector `periodicLerayProjector` | `IsSolenoidalPeriodicDatum` (`Σ_j 2πi k_j A_j(k) = 0`), `periodicLeray` (formula), `IsPeriodicLerayDatum A B` (graph) | **B** (projector + solenoidal predicate + graph relation), naming as B. |
| pressure gauge | `HasZeroPressureMeanT I p` | `PressureGaugeT I p` | **B's name**. |
| classes | `initialClassT`, `forceClassT` | `initialClassT` (smooth, unit-periodic, divergence-free; **no mean-zero condition**), `MemForceT`/`forceClassT` (smooth, unit-periodic, compact time support `K ⊂ (0,∞)`) | **verify against the paper**: the spec lane must quote the exact lines of `03-torus.tex`/`02-preliminaries.tex` defining `𝒳_𝕋` and `𝓕_𝕋` and settle (i) whether `𝒳_𝕋` allows nonzero mean (B says yes), (ii) the time-support/decay clause of `𝓕_𝕋`. Both drafts' citations go into `COMPARISON.md`; if they disagree with each other, the paper line decides. |
| breakdown set | `breakdownSetT ν a T` | `breakdownSetInT Y ν a T` + `breakdownSetT` | **B** (parametric `Y`, matching `Data.lean:672`). |
| regularity notion | — | `RegularThroughT` | keep (mirrors `Data.lean:665`). |
| `ClassicalSolutionT` fields | `velocity_periodic`, `pressure_periodic`, `pressure_gauge`, `initial`, … | similar | **cross-check against Section 4's `ClassicalSolutionR` (`Data.lean:624-656`)**: keep the same field names/order where the clause exists on both domains (`horizon_pos`, `velocity_smooth`, `pressure_smooth`, `initial`, `divergence`, `momentum`, `sobolev` (a continuous datum path at every order), `pressure_gradient`, …) and add only the torus-specific `velocity_periodic`, `pressure_periodic`, `pressure_gauge`. |
| energy norm | `energyENormT` | `energyEssSupT + energyGradientT` | **B's split** (`E_T` = `L^∞_t L²_x + L²_t Ḣ¹_x` on the torus), named `energyENormT`. |
| homogeneous data | absent | absent | **add** (T12/T13 need it): `IsPeriodicHomogeneousDatum s z A` with weight `|2πk|^s` (`A(0) = 0` forced) and `periodicHomogeneousENorm s z` — copy the shape from `research/T13/RECONCILIATION.md` §2 / T12 draft A (`homogeneousDatumWeight`), so that T12/T13/T20 import one definition. |

## 3. Decisions
Base the reconciled `research/T10/Spec.lean` on **B**, importing A's more precise docstrings/citations and A's needs-a-lemma list; add the homogeneous datum/norm; name the future contract `Contracts/V1/TorusData.lean`, structure `TorusDataAPI` (the *definitions* are the deliverable — the registered contract's fields are the basic facts every consumer needs: datum uniqueness, `IsPeriodicDatum` real, Parseval/`TorusCube` bridge both ways, mean decomposition identities, Leray is a contraction/projector commuting with the weight, mean-zero preservation, pressure gauge preserves the equation, `energyENormT` ≡ physical energy norm, the `ClassicalSolutionR`-style transports).

## 4. Next
Lane 277: reconciled `research/T10/Spec.lean` + merged `COMPARISON.md` (+ provenance copies); then the T13/T12/T16/T14/T22 spec lanes import it; then T10's proof lanes (the "needs a lemma" list) and registration `T01.torus_data`.
