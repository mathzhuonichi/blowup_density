# R41D — reconciliation decisions and risk notes

Output: `research/R41D/Spec.lean`, namespace
`BlowupDensity.R41D.Draft`, with two concrete `def`s and one
`structure RDensityAPI (Y : Set SpaceTimeField)`.

The clause-by-clause evidence and consolidated gap table are in
`COMPARISON.md`.  The authoritative paper passages are
`paper/sections/04-whole-space.tex:7-13,176-195`; the R42 family being retained
is stated at `:31-43`.

## 1. Decisions

| Clause | Decision | Reason |
|---|---|---|
| Size of the contract | Keep the expanded density conclusion **and** the typed two-case witness; do not add separate copies of R42 fields. | The theorem statement at `:10` alone would support Draft B, but the frozen R41D task explicitly requires the split at `:177`, and R45/R46 need the compact-difference provenance that a bare density existential forgets. Packaging one existing R42 record preserves that evidence without creating sibling-statement drift. |
| Ambient force class | `RDensityAPI` is parameterized by `Y`, with `forceClass : IsR41DForceClass Y`. | Draft A's parameterization lets each consumer request one class instance. Draft B's universal `Y` binder is defensible but unnecessarily bundles proofs for all three classes into one object. |
| Force-class selector | Keep Draft B's named `IsR41DForceClass`. | It makes the `F_R` / `F_c` / `F_rd` restriction reusable and readable; the definition is fully concrete, not a placeholder proposition. |
| Breakdown membership | Use `f in breakdownSetIn Y nu a T`. | This is Draft B's canonical registered spelling and definitionally equals Draft A's explicit pair `f in Y` and `T_max(a,f) <= T`. It keeps the same `Y` on both sides of the relative density statement. |
| Quantifier order | In each branch: global `nu,T,s`, then `forall a`, `forall g`, `forall radius`, `exists f`. | Matches the task card and the proof's “Fix `a,g` and a positive radius” at `:177`. |
| Time exponents and thresholds | Two fields: `densityL1` with `s < 1/2`; `densityL2` with `s < -1/2`. | These are the literal specializations of `s_q=2/q-3/2` at `:8,13`; neither endpoint belongs to the density range. |
| First branch | The result contains `T_max(a,g) <= T` and `f=g`. | Adopts Draft A. Line `:177` mandates this witness, and its unchanged-class property is needed by subclass consumers. |
| Second branch | The result contains the strict opposite and `R42InsertedWitness nu T a g f`. | Adopts Draft A. It records a positive margin, one selected `epsilon`, compact force difference, and exact lifespan, all aligned to the surrounding datum. |
| R42 record version | Use the fully qualified `Contracts.V2.InsertionLifespan.InsertionLifespanV2API`. | It extends the registered V1 lifespan record and retains the full-horizon solution, maximal identification, and displayed blow-up. Qualification avoids the frozen V1 short-name collision. |
| Same-family rider | Retain the whole V2 object and align `family.a`, `.g`, `.T`, and `family.force epsilon`; do not restate `initial`, `history`, `energyRate`, or `forceConvergence` as R41D fields. | Lines `:13,179` say the history and energy assertions come from the insertion theorem. One package ensures they concern the same family, while direct restatement would duplicate a sibling contract. |
| Rapid initial class | Keep `a in initialClassR` for every `Y`, including `F_rd`. | Line `:195` first says Theorem 4.1 remains valid under class replacement. Its Schwartz sentence is an “in particular” consequence via `initialClassSchwartz subset initialClassR`, gap G4, not a weakening of the main quantifier. |

The resulting statement strictly implies Draft B's extensional density fields:
forget the final disjunction and unfold `breakdownSetIn`.  Draft B does not imply
the reconciled result, because no Lean term can recover an R42 family or its
compact-difference field from a comment.

## 2. Risk audit: ways a wrong shape becomes false, weak, or vacuous

| Choice under audit | Failure mode if chosen incorrectly | Guard in `Spec.lean` |
|---|---|---|
| `nu,T > 0` | If `T <= 0`, `ENNReal.ofReal T = 0`; the breakdown condition can collapse onto the empty-supremum convention. If `nu <= 0`, neither the packet nor the PDE theorem is the manuscript's statement. | Both positivity hypotheses precede every density clause. |
| `maximalLifespanR` empty supremum | `Data.maximalLifespanR` is `0` when no classical solution exists. A contract omitting `a in initialClassR` or force admissibility could call nonexistence “breakdown by `T`” and become spuriously easy. | References satisfy `a in initialClassR` and `g in Y`; approximants lie in the same selected manuscript class. The inserted branch additionally has `T_max(a,f)=ofReal T>0`. The first branch still relies on the local-existence stack for the mathematical nonzero-lifespan fact. |
| Empty ambient or breakdown sets | `forall g in Y` is vacuous if `Y` is empty; conversely, density in a genuinely nonempty `Y` cannot hold if its relative breakdown set is empty. | `Y` is definitionally one of the three manuscript classes, rather than an arbitrary set. D01/R45 should still export `0` membership for the compact and rapid classes when proving nonempty critical balls; this is a non-vacuity check, not an extra R41D hypothesis. |
| `ENNReal`-valued force norms | Routing through `.toReal` would turn `top` into `0`, so a missing datum path could look arbitrarily small and make the theorem false. Permitting `<= radius` would also admit a zero-radius boundary not used by density. | Norms stay in `ENNReal` and use strict `< radius`; `top < radius` is false even when `radius=top`. Quantification over every positive radius includes arbitrarily small finite radii, so the allowed `top` radius does not weaken density. |
| Threshold signs/endpoints | Using `s <= 1/2`, `s <= -1/2`, or reversing the sign in the `q=2` branch would assert density at/above the sharp threshold and conflict with Theorem 4.1(ii). | Literal strict hypotheses `s < 1/2` and `s < -1/2`. |
| Split guards | Two strict guards would omit `T_max=T`; two weak guards would overlap and allow the inserted arm where the paper says to use `g`. | First guard is `T_max<=ofReal T`; second is its strict linear-order complement `ofReal T<T_max`. |
| Quantifier order | Moving `exists f` before `g` or before `radius` would ask for one approximant that works for every reference/radius; moving the radius outside `g` can also change the topology. Either is a different theorem. | Literal `forall a -> forall g -> forall radius -> exists f`. |
| Bare density versus proof provenance | A bare `exists f` is true if density is true, but it forgets whether subclass closure came from `f=g` or a compact correction. R45/R46 then cannot recover the manuscript proof from the contract. | The final disjunction is part of each witness. |
| Mixing R42 families | Choosing `epsilon` from one family's convergence, lifespan from another, and history from a third can satisfy individually plausible existential clauses while proving nothing about the returned `f`. | One existential `L`, one `epsilon`, and equations aligning `a,g,T,f`. |
| V1 versus V2 lifespan object | The frozen short name `InsertionLifespanAPI` can resolve to the old three-field record, losing `memForce`/`regular` or the V2 solution/maximal/blow-up exports depending on namespace. | The V2 type is fully qualified. |
| Margin strength | A bare `ClassicalSolutionR ... (T+delta)` lives on the half-open interval `[0,T+delta)` and yields only a non-strict lifespan lower bound. Treating it as regular *through* that endpoint would be invalid. | The witness retains both `RegularThrough ... (T+margin)` and the strict `referenceLifespan` inequality, in addition to the family's half-open reference solution. |
| `Ico` versus `Icc` solution windows | Replacing the inserted solution's `[0,T)` (`Ico 0 T`) by `[0,T]` (`Icc 0 T`) demands a classical value at the singular time and can make the insertion clause false. Replacing the closed earlier-history window `0 <= t <= T-2 epsilon^2` by a half-open one silently loses the displayed endpoint at `:36`. | These windows are not redefined: the packaged `InsertionFamilyAPI` keeps `velocity_smooth` on `Ico 0 T` and `history` with both endpoint inequalities. |
| Full force-time norm versus a finite window | Measuring only on `Ico 0 T` or `Icc 0 T` ignores the post-`T` part of the compact correction. That would be a weaker and potentially false transcription of relative density in `L^q(0,infinity;H^s)`. | `forceSobolevENormL1/L2` use `forceTimeMeasure`, the full open positive half-line. |
| `epsilon` interval | Replacing R42's `Ioc 0 epsilon_0` by a set containing `0` could select the limiting, non-inserted object; demanding `Icc` would do exactly that. | The selected parameter is in `Ioc (0:Real) family.epsilon_0`, exactly the registered family range. |
| Difference orientation | The R42 field is compactness of `f-g`. Accidentally asking for an unrelated compact `h`, or measuring `f-(g+h)`, would not prove class preservation for the returned witness. | Both the compactness clause and the norm use the same physical difference `f-g`. |
| Rapid-decay closure | `F_rd` is not definitionally closed under adding a compact correction, and its inclusion into `F_R` is not currently registered. Assuming either by simplification would leave the rapid instance unproved. | The statement asserts membership in the same `Y`; G2 and G3 explicitly record the two proof obligations. |

## 3. Upstream work that remains

The open proof-interface items are G1--G5 of `COMPARISON.md`:

1. assemble an aligned R42 V2 family from the strict-lifespan side of the split;
2. prove `F_rd subset F_R`;
3. prove `F_rd` is stable under an `F_c` difference;
4. prove `S_sigma subset X_R` for the highlighted specialization;
5. prove the zero physical force has zero `forceSobolevENorm` at both exponents.

The margin-selection theorem, `F_R` compact-difference closure, `F_c subset
F_R`, and compact additivity are already registered; they are inputs to G1 or
local assembly, not new gaps.
