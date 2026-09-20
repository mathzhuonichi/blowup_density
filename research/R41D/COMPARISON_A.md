# R41D draft A — source/Lean comparison

This compares `research/R41D/DraftA.lean` only with the permitted sources for
lane 171: the cited manuscript lines, `collaboration/tasks/R41D.md`,
`PLAN.md` §9's single R41D DAG note, and the listed `Contracts.V1`/`V2` files.
No other R41D draft, no pre-existing `research/R41D/` file, no other worktree,
and no R41D entry in `research/section4/STATEMENTS.md` was inspected or searched.

## Paper clause ↔ Lean field

| Paper clause | Lean declaration / field | Exact spelling and fidelity note |
|---|---|---|
| `04-whole-space.tex:8`: fix `ν,T>0` | `RDensityAPI.subcriticalL1`, `subcriticalL2` | Both start `∀ ν, 0 < ν → ∀ T, 0 < T → …`. |
| `:8-10`: relative `L^q(0,∞;H^s)` topology and density for every fixed `a∈X_R` | Both density fields | `∀ a : SpatialField, a ∈ initialClassR → ∀ g, g ∈ Y → ∀ r : ℝ≥0∞, 0 < r → ∃ f`; this is the task-card order `∀ a ∀ g ∀ radius ∃ f`. |
| `:10`: `B^R_{ν,a,T}` | Both density fields | The returned conjunction `f ∈ Y ∧ maximalLifespanR ν a f ≤ ENNReal.ofReal T` is definitionally the membership condition of `breakdownSetIn Y ν a T`. |
| `:8,13`: `q=1`, `s<s₁=1/2` | `subcriticalL1` | Literal hypothesis `s < (1 : ℝ) / 2`; distance is `forceSobolevENormL1 s (f-g) < r`. |
| `:8,13`: `q=2`, `s<s₂=-1/2` | `subcriticalL2` | Literal hypothesis `s < -(1 : ℝ) / 2`; distance is `forceSobolevENormL2 s (f-g) < r`. |
| `:177`: split at `T_max(a,g)≤T` | Last disjunction of both density fields | First arm is `maximalLifespanR ν a g ≤ ofReal T ∧ f = g`; second arm starts `ofReal T < maximalLifespanR ν a g`.  Since `ℝ≥0∞` is linearly ordered, these are the two exhaustive cases used in the proof. |
| `:177`: otherwise choose a positive margin beyond `T` and apply Theorem 4.2 | `R42InsertedWitness` | Packages a registered `InsertionLifespanV2API`; aligns `family.a=a`, `family.g=g`, `family.T=T`; records `0 < family.margin`, `RegularThrough … (T+margin)`, and `referenceLifespan`. |
| `:177`: choose sufficiently small `ε` so the force difference is inside the prescribed radius | `subcriticalL1` / `subcriticalL2` plus `R42InsertedWitness` | `ε ∈ Ioc 0 family.ε₀`, `f = family.force ε`, and the corresponding final norm inequality.  Selection consumes `InsertionFamilyAPI.forceConvergence` at `q=1` or `q=2`. |
| `:177`: inserted force has the same initial velocity and lifespan exactly `T` | `R42InsertedWitness` | Same initial velocity is carried by the packaged `family.initial`; the explicit final conjunct `maximalLifespanR ν a f = ofReal T` is `InsertionLifespanAPI.lifespan` after alignment. |
| `:13,179`: same earlier history and `E_T` convergence for a regular reference | Packaged R42 V2 record | `family.history` and `family.energyRate` are fields of the same family.  They are not duplicated as independent R41D fields because this deliverable is the density branch, but the nontrivial witness retains them rather than forgetting which insertion produced `f`. |
| `:183-195`: replace `F_R` by `F_c` or `F_rd` | `RDensityAPI.forceSubclass` and `f ∈ Y` | `Y` is restricted to `forceClassR`, `forceClassCompact`, or `forceClassRapid`; reference and approximant both lie in the selected relative class. |
| `:195`: in particular, rapidly decaying forces and `a∈S_σ` | `Y = forceClassRapid` specialization | The density fields are stated for all `a∈initialClassR`, which is the literal “Theorem remains valid” clause and is stronger than its stated Schwartz specialization.  Recovering that specialization as a typed corollary needs the inclusion gap G4 below. |

## Choices forced by the registered vocabulary

| Manuscript language | Contract spelling chosen | Why |
|---|---|---|
| A smooth initial datum `a∈X_R` | `a : SpatialField`, `a ∈ initialClassR` | `initialClassR` is the registered `H^∞∩L²_σ` set. |
| A reference/approximating force | `g f : SpaceTimeField` | All three force subclasses are predicates/sets on this common type, so the same `maximalLifespanR` applies to each. |
| `F_R`, `F_c`, `F_rd` | `forceClassR`, `forceClassCompact`, `forceClassRapid` | Set-valued forms make relative membership `g∈Y`, `f∈Y` uniform.  The corresponding predicates are `MemForceR`, `MemForceCompact`, and `MemForceRapid`. |
| Density in `L¹_tH^s_x` | `forceSobolevENormL1 s (fun z => f z - g z) < r` | This is the registered Bochner norm on `(0,∞)`, with an `ℝ≥0∞` radius matching `Data.RelativelyDense`. |
| Density in `L²_tH^s_x` | `forceSobolevENormL2 s (fun z => f z - g z) < r` | Same choice at exponent two; no finite-time truncation is used. |
| Relative topology | Explicit `g∈Y`, `f∈Y`, positive radius | This is the epsilon-ball expansion of `Data.RelativelyDense`; it also permits the task-required `∀a ∀g ∀r` ordering and visible proof split. |
| Blow-up forces `B^R_{ν,a,T}` in a selected subclass | `f ∈ Y ∧ maximalLifespanR ν a f ≤ ENNReal.ofReal T` | This is `breakdownSetIn Y ν a T`, not `breakdownSetR`, because the latter fixes `Y=F_R` and would lose subclass parameterization.  No `breakdownSetRZero` is used: this lane is only the positive/density direction for arbitrary fixed `a`. |
| Breakdown by `T` | `maximalLifespanR … ≤ ENNReal.ofReal T` | This is exactly the preliminary definition.  No extra `breakdownSetR*` or speed-blow-up condition is added to the density conclusion. |
| “Reference exists through `T+δ`” | `RegularThrough ν a g (T + family.margin)` plus `referenceLifespan` | The registered R42 lifespan record uses this exact horizon and additionally exports the strict maximal-lifespan inequality. |
| The inserted family | `Contracts.V2.InsertionLifespan.InsertionLifespanV2API` | The qualified V2 name avoids the frozen unregistered short-name collision and retains the V1 `regular`, `referenceLifespan`, `lifespan` fields together with the full-horizon solution/maximality exports. |
| Compact force correction | `MemForceCompact (fun z => f z - g z)` | This is the exact conclusion of `InsertionFamilyAPI.forceDifference_compact` after aligning `f` and `g`; it is the input needed for preservation of all three selected subclasses. |
| First branch “take `f=g`” | An explicit disjunct with `f = g` | A bare `RelativelyDense` field would erase this mandated construction choice. |
| Second branch “insert” | `R42InsertedWitness` | A bare existential force with lifespan `T` would erase the fact that the norm estimate, compact correction, history, and lifespan all come from the same R42 `ε`-family. |

## Upstream gaps exposed by draft A

These are absent from the permitted contract inputs.  They are proof-interface
gaps, not placeholders in the statement.

| ID | Exact missing shape needed | Why R41D needs it | Owner |
|---|---|---|---|
| G1 | A direct R42 entry point of the shape `∀ ν>0, ∀ T>0, ∀ a∈initialClassR, ∀ g, MemForceR g → ENNReal.ofReal T < maximalLifespanR ν a g → ∃ P L, L.family.a=a ∧ L.family.g=g ∧ L.family.T=T`, with `L : Contracts.V2.InsertionLifespan.InsertionLifespanV2API ν P`. | `insertionFamilyStatement` is conditional on a pre-existing `ScalingAPI` and aligned reference solution, while `insertionLifespanV2Statement` is conditional on a pre-existing `InsertionFamilyAPI`.  The density assembly starts only from `a,g,T` and a long-lifespan inequality. | R42, with A02 supplying reference/maximal-solution selection. |
| G2 | Margin selection: `ENNReal.ofReal T < maximalLifespanR ν a g → ∃ δ : ℝ, 0 < δ ∧ RegularThrough ν a g (T+δ)` (under `ν>0`, `a∈initialClassR`, `MemForceR g`, `T>0`). | This is the exact bridge from the second side of the split to R42's `regular` hypothesis.  It was not found as an exported field in the listed contracts. | A02 maximal-lifespan API. |
| G3 | Compact-perturbation closure for each selected class: at minimum `g∈Y → MemForceCompact h → (fun z => g z + h z)∈Y` for `Y=forceClassR`, `forceClassCompact`, and `forceClassRapid`; also `MemForceCompact g → MemForceR g` and `MemForceRapid g → MemForceR g` so the subclass references meet R42's inherited `memForce` field. | R42 exports only that `g_ε-g` is compact.  R41D must conclude `g_ε∈Y`, including preservation of every rapid-decay seminorm. | D01 force-class closure. |
| G4 | `initialClassSchwartz ⊆ initialClassR`. | It turns the rapid-class instance, stated for `a∈X_R`, into the explicit `a∈S_σ` “in particular” clause of `04-whole-space.tex:195`.  Both sets are defined in `Data.lean`, but the inclusion is not an assertion there. | D01 datum/class lemmas. |
| G5 | Zero-difference norm at both exponents, e.g. `forceSobolevENorm 1 s (fun z => g z-g z)=0` and the exponent-two analogue for admissible `g`. | The first branch uses `f=g`; the positive-radius conclusion then needs the registered datum-path norm to reduce to zero.  This should be a small norm-vocabulary lemma, but it is not a field of the listed contracts. | D01 norm/datum lemmas. |

## Draft-A judgment calls for later comparison

1. The API is parameterized by a set `Y` and carries a concrete three-way
   equality field, rather than defining three duplicated structures.  This
   preserves one theorem shape while preventing accidental instantiation at an
   unrelated force class.
2. The two sharp thresholds are separate fields instead of one `q∈{1,2}`
   field.  This avoids coercion bookkeeping around `criticalOrder q.toReal` and
   makes both topologies visible in the contract surface.
3. The result is intentionally stronger than a bare `RelativelyDense` field:
   it remembers which arm of the manuscript proof produced the witness.  That
   strengthening is explicitly requested by the R41D task card and is fully
   witnessed by registered objects, not by an abstract proposition.
4. The density fields keep the general initial class `initialClassR` even for
   `Y=forceClassRapid`, following “Theorem 4.1 remains valid” at line 195.  The
   Schwartz formulation is a corollary once G4 is registered.

