# R41D — reconciled comparison of the two blind drafts

Scope: the subcritical density branch of Theorem 4.1, statement
`paper/sections/04-whole-space.tex:7-13`, proof `:176-179`, together with the
force-class replacement at `:183-195`.  The R42 object used by the proof is
stated at `:31-43`.  The two inputs are `DraftA.lean` and `DraftB.lean`; the
output is `Spec.lean`.

The cited source ranges were read directly with `sed -n '7,30p'`,
`sed -n '176,195p'`, and, for the R42 record, `sed -n '30,62p'`.  Numbered
copies were separately checked with `nl -ba ... | sed -n`.

Legend: **A** or **B** means that draft's shape wins; **both** means the two
shapes are definitionally or propositionally the same; **hybrid** means one
draft supplied the logical shape and the other the canonical registered name.

## 1. Clause-by-clause paper comparison

| Paper clause | Draft A | Draft B | Reconciled decision and fidelity ruling |
|---|---|---|---|
| `:8`, fix `nu,T>0` and `q in {1,2}` | Two fields, each quantifying `nu,T` with positivity hypotheses. | Same. | **Both.** Separate `q=1` and `q=2` fields keep the two thresholds and registered norm abbreviations literal. |
| `:10`, “for every fixed `a in X_R`” | `forall a, a in initialClassR`. | Same. | **Both.** `Data.initialClassR` is the registered `X_R` (`Contracts/V1/Data.lean:509`). |
| Task-card order `forall a forall g forall radius exists f`; proof `:177` begins by fixing `a,g,radius` | After the global `nu,T,s`, literally `forall a`, `forall g`, `forall r`, `exists f`. | Same, with `Y` quantified before the global parameters. | **Both on the load-bearing order.** The reconciled field keeps `a -> g -> radius -> f`; no choice of `f` may depend on a later reference or radius. |
| `:8-10`, relative topology on the selected smooth force class | Structure parameter `Y`; a `forceSubclass` field restricts it; both `g` and `f` lie in `Y`. | `Y` and `IsR41DForceClass Y` are quantified inside each field. | **A.** Both are logically defensible, but a parameterized `RDensityAPI Y` is the repository's requested class-parametric R41D interface: R41, R45, and R46 can consume exactly the `F_R`, `F_c`, or `F_rd` instance they need without requiring one proof object to bundle all three. |
| `:8,13`, `L^1_t H^s_x`, `s < 1/2` | `forceSobolevENormL1 s (f-g) < radius` and strict `s < (1:Real)/2`. | Same, with `s < 1/2`. | **Both.** The reconciled spelling is explicit about the real numeral. Endpoint `s=1/2` is excluded exactly as `:10,13` require. |
| `:8,13`, `L^2_t H^s_x`, `s < -1/2` | `forceSobolevENormL2 s (f-g) < radius` and strict `s < -(1:Real)/2`. | Same, with `s < -(1/2)`. | **Both.** Endpoint `s=-1/2` is excluded. The norm is the full `(0,infinity)` norm, not a finite-time restriction. |
| `:10`, approximant belongs to the relative breakdown set | Spells `f in Y` and `maximalLifespanR nu a f <= ofReal T` separately. | Uses `f in breakdownSetIn Y nu a T`. | **B's spelling, A's truth conditions.** `Data.breakdownSetIn` expands to exactly A's conjunction (`Data.lean:672-674`); using the registered name prevents a later drift in the definition of the singular set. |
| `:177`, split at `T_max(a,g) <= T` | A disjunction in the result type: the first arm contains the inequality and `f=g`; the second contains the strict opposite and an R42 witness. | The result type contains only density; the split and `f=g` occur only in docstrings. | **A.** B is faithful to the extensional theorem at `:10`, but incomplete for this frozen R41D task: the task card explicitly requires the split, and downstream subclass density needs to know that the first witness is unchanged and the second has compact difference. In `ENNReal` the two comparisons are exhaustive. |
| `:177`, first case “take `f=g`” | Literal `f = g` in the first disjunct. | Documentation only. | **A.** This is the manuscript's stated witness, not merely one possible implementation. The external norm inequality then reduces to the zero-difference lemma G5. |
| `:177`, otherwise choose a positive margin beyond `T` | The second arm has `ofReal T < T_max(a,g)` and `R42InsertedWitness`; that definition records a positive family margin, `RegularThrough` at `T+margin`, and a strict reference-lifespan inequality there. | Documentation names V1/V2 `regular` and `referenceLifespan`, but no margin or R42 object occurs in the field type. | **A.** The explicit clauses are faithful to “choose `delta>0` so that the reference exists through `T+delta`”. The stronger `RegularThrough` form matches the registered lifespan contract and guarantees room beyond the half-open reference horizon. |
| `:177`, choose sufficiently small `epsilon` and insert | Existentially selects one `epsilon in (0,epsilon_0]`, sets `f` equal to that family's force, and places the requested norm inequality on the same `f`. | Mentions `force` and `forceConvergence` only in the docstring. | **A.** The typed alignment prevents using convergence from one family and lifespan from another. The `q=1` and `q=2` fields select through the same general `forceConvergence` projection at their respective exponents. |
| `:177`, same initial velocity and lifespan exactly `T` | Packages a V2 lifespan record; explicitly repeats `T_max(a,f)=ofReal T`; `family.initial` is retained through the package. | Density asks only `T_max<=T`; exact lifespan and initial preservation are documentation. | **A.** Exact lifespan is the stronger R42 conclusion at `:34` and is stated again in the proof at `:177`. It implies the weaker breakdown membership because `T>0`. |
| `:13,179`, same earlier history and velocity difference tending to zero in `E_T` | The selected V2 record contains the same `InsertionFamilyAPI`, hence its `history` and `energyRate` fields. | Documentation lists `history`/energy informally, but the declaration retains no family. | **A.** Line `:179` says these assertions are part of the insertion theorem. Packaging the one family is the least duplicative way to preserve them without restating sibling fields in R41D. |
| `:183-195`, replace `F_R` by `F_c` or `F_rd` | `Y` is restricted by a three-way equality field. | A local `IsR41DForceClass` definition and a universal `Y` binder. | **Hybrid.** Keep B's named predicate, but A's structure parameter. Both correctly thread the same `Y` through reference and approximant. |
| `:192,195`, rapid-decay formulation highlights `a in S_sigma` | Keeps the stronger general assumption `a in initialClassR`; records a missing inclusion. | Same. | **Both.** Line `:195` first says Theorem 4.1 remains valid, so the `X_R` statement wins; the “in particular” Schwartz sentence follows through G4 rather than replacing the theorem's initial class. |

## 2. Registered objects used by each draft

| Role | Draft A | Draft B | Reconciled use |
|---|---|---|---|
| Ambient classes | `forceClassR`, `forceClassCompact`, `forceClassRapid` directly in `forceSubclass`. | Same three names through `IsR41DForceClass`. | `IsR41DForceClass Y`, with `Y` a structure parameter. Definitions are `Data.lean:553,563,578`. |
| Breakdown set | Expands membership as `f in Y` plus `maximalLifespanR ... <= ofReal T`. | Direct `breakdownSetIn Y nu a T`. | Direct `breakdownSetIn`; it is definitionally A's conjunction. Neither `breakdownSetR` (hard-coded `F_R`) nor `breakdownSetRZero` (wrong initial datum) is used. |
| Lifespan | `maximalLifespanR` in the breakdown condition, both split guards, the margin inequality, and exact inserted lifespan. | Appears only through `breakdownSetIn` in the declaration; exact lifespan is discussed in docstrings. | Both the canonical breakdown membership and explicit guards/exact equality. `maximalLifespanR` is `ENNReal`-valued (`Data.lean:657-658`). |
| Force norms | `forceSobolevENormL1` / `forceSobolevENormL2` on the physical difference. | Same. | Same. They abbreviate the measurable-datum-path infimum `forceSobolevENorm` (`Data.lean:225-236`), so missing data fail to `top`, never to a small real. |
| R42 base family | A's result contains `L.family : Contracts.V1.InsertionFamilyAPI nu P`. | Imports and docstrings name `InsertionFamilyAPI`, but neither result field mentions it. | Retained existentially. Its relevant projections are `force`, `initial`, `history`, `forceDifference_compact`, `energyRate`, and `forceConvergence` (`InsertionFamily.lean:168-172,203-206,224-226,265-268,313-327`). |
| R42 V1 lifespan object | Reached through the V2 extension: `memForce`, `regular`, `referenceLifespan`, `lifespan`. | Imported and named only in prose. | Retained through V2. These four clauses are `Contracts/V1/InsertionLifespan.lean:117-137`. |
| R42 V2 lifespan object | Qualified `Contracts.V2.InsertionLifespan.InsertionLifespanV2API`; aligned to `a,g,T` and one selected `epsilon`. | Imported and named only in prose. | A's qualified object wins. Besides inherited clauses it co-carries full-horizon `solution`, maximal-solution identification, and the displayed blow-up (`Contracts/V2/InsertionLifespan.lean:117-158`). |
| Reference margin | Explicit positive `family.margin`, `RegularThrough`, and `referenceLifespan`. | Prose reference to `regular` and `referenceLifespan`. | Explicit, as part of `R42InsertedWitness`. `family.margin` projects `scaling.correction.delta`, whose positivity is structural. |
| Same-family guarantee | Existential package plus equations `family.a=a`, `family.g=g`, `family.T=T`, `f=family.force epsilon`. | None in the declaration. | A. This is what lets a consumer project history, energy, convergence, and lifespan for one and the same inserted solution. |

Draft B's density proposition is therefore mathematically correct but forgetful:
it is a consequence of the reconciled API after dropping the final disjunction.
The converse is not recoverable from B's type, because comments cannot supply an
R42 family or a compact-difference proof to a Lean consumer.

## 3. Consolidated upstream gap table

“Blocks” distinguishes formation of the statement from its proof.  None of the
open items prevents `Spec.lean` from elaborating: every proposition there is
already concrete.  They are missing reusable proof interfaces or proof lemmas.

| ID | Owner | Exact Lean shape needed | Blocks | Found by |
|---|---|---|---|---|
| **G1** | **R42 assembly with A02 selection** (or the R41D assembly lane if kept consumer-local) | `∀ (ν : ℝ), 0 < ν → ∀ (T : ℝ), 0 < T → ∀ (a : SpatialField), a ∈ initialClassR → ∀ (g : SpaceTimeField), MemForceR g → ENNReal.ofReal T < maximalLifespanR ν a g → ∃ (P : PacketAPI ν) (L : Contracts.V2.InsertionLifespan.InsertionLifespanV2API ν P), L.family.a = a ∧ L.family.g = g ∧ L.family.T = T`. The record itself then supplies the positive margin and every R42 clause. | **Proving** the second arm. It does not block stating it. The registered R42 statements currently begin from preassembled correction/scaling/family objects. | A-G1 and B-G1. |
| **G2** | **D01 force-class layer**, consumed by R41D/R45 | `∀ f : SpaceTimeField, MemForceRapid f → MemForceR f` (equivalently `forceClassRapid ⊆ forceClassR`). | **Proving** the rapid-class second arm: the V1 lifespan record requires `MemForceR family.g`. | B-G2; part of A-G3. |
| **G3** | **R45 / D01 rapid-class closure** | `∀ (g f : SpaceTimeField), MemForceRapid g → MemForceCompact (fun z => f z - g z) → MemForceRapid f`. | **Proving** that the inserted witness returns to `F_rd`. | B-G3; part of A-G3. |
| **G4** | **D01 initial-class layer**, consumed by R45 | `initialClassSchwartz ⊆ initialClassR`. | **Proving the typed `S_sigma` specialization** at `:195`; it does not block the stronger `a in X_R` R41D statement. | A-G4 and B-G4. |
| **G5** | **D01 norm vocabulary** | At minimum `∀ (q : ℝ≥0∞), (q = 1 ∨ q = 2) → ∀ (s : ℝ), forceSobolevENorm q s (0 : SpaceTimeField) = 0`; with pointwise `g - g = 0`, this supplies both registered abbreviations. | **Proving** the first arm's strict radius inequality when `f=g`. | A-G5. |

### Reported gaps that are already closed or are local algebra

| Blind-draft item | Current ruling |
|---|---|
| A-G2, selecting a positive regularity margin from `ofReal T < T_max` | **Not an open upstream gap.** `Contracts.V1.MaximalPartial.MaximalPartialAPI.regularThrough_iff` gives `RegularThrough nu a g T <-> ofReal T < T_max` and `referenceLifespan` selects a positive margin with a realized longer horizon and strict lifespan inequality (`MaximalPartial.lean:200-214`). G1 still has to assemble that output into the R42 chain. |
| A-G3's `F_R` compact-difference closure | **Registered.** `DatumLemmasAPI.memForceR_of_compact_difference` has exactly `MemForceR g -> MemForceCompact (gEpsilon-g) -> MemForceR gEpsilon` (`DatumLemmas.lean:381-383`). |
| A-G3/B note for `F_c` | **No mathematical gap.** `memForceCompact_add` is registered (`DatumLemmas.lean:353-355`); rewriting `f = g + (f-g)` is local algebra. |
| Compact references entering R42 | **Registered.** `DatumLemmasAPI.memForceCompact_memForceR` supplies `F_c subset F_R`. Only the rapid analogue remains G2. |
| Selecting a sufficiently small `epsilon` from convergence | **No extra field needed.** `InsertionFamilyAPI.forceConvergence` is a genuine `Tendsto` statement (`InsertionFamily.lean:323-327`); the positive radius and `eps_pos` give an eventual point in `(0,epsilon_0]`. |

## 4. Net reconciliation

The reconciled record is Draft A's typed, class-parametric two-case theorem,
with Draft B's named force-class predicate and canonical `breakdownSetIn`
membership.  It retains exactly one R42 V2 family instead of copying any of its
fields into the R41D structure.  This makes the extensional density statement
available immediately while preserving the stronger evidence required by the
task card and by the compact/rapid consumers.
