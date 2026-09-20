# R41D blind draft B: paper-to-Lean comparison

This comparison covers only the subcritical density direction of Theorem 4.1
and the force-class parameterization requested by the task card. It does not
state or analyze the zero-data converse.

## Paper clause ↔ Lean field

| Paper clause | Lean transcription in `DraftB.lean` | Contract vocabulary / reason |
|---|---|---|
| `04-whole-space.tex:7-8`: fix `nu,T>0`, `q in {1,2}`, and use the relative `L^q(0,infinity;H^s(R^3))` topology | Both `RDensityAPI.densityL1` and `densityL2` quantify `nu,T` with positivity hypotheses; the two values of `q` are separate fields | Separate fields avoid an `ENNReal.toReal` conversion in the threshold and use the registered abbreviations `forceSobolevENormL1` and `forceSobolevENormL2` directly |
| `:8,13`: `s_q=2/q-3/2`, hence thresholds `1/2` and `-1/2` | `densityL1` assumes `s < 1 / 2`; `densityL2` assumes `s < -(1 / 2)` | These are the two literal specializations of `Data.criticalOrder`; no endpoint is included |
| `:10`: for every fixed `a in X_R` | `forall a : SpatialField, a in initialClassR` in both fields | `Data.initialClassR` is the registered `H^infinity cap L^2_sigma` class from `02-preliminaries.tex:12-15` |
| `:8-10`: density relative to the ambient smooth force class | `forall g : SpaceTimeField, g in Y`, then `forall r : ENNReal, 0 < r`, then an approximant `f` | This is the epsilon/radius expansion of `Data.RelativelyDense`, written out to expose the required task-card order `forall a forall g forall radius exists f` |
| `02-preliminaries.tex:42-44`: `B^R_{nu,a,T}={f in F_R:T_max(a,f)<=T}` | `f in breakdownSetIn Y nu a T` | `breakdownSetIn` is used instead of `breakdownSetR`, because the latter hard-codes `F_R`; it expands to both `f in Y` and `maximalLifespanR nu a f <= ENNReal.ofReal T` |
| `04-whole-space.tex:176-177`: if `T_max(a,g)<=T`, take `f=g` | The result fields contain the density existential; their docstrings pin `f=g` as the required implementation choice in this case | The equality is a proof-witness choice, not an additional conclusion of the theorem. Adding it to the result type would strengthen the published density statement for no downstream mathematical need |
| `:176-177`: otherwise choose positive lifespan beyond `T`, insert, and make the force difference smaller than the prescribed radius | The second-case source is documented as R42's one family: `InsertionFamilyAPI.force`, `.forceConvergence`, `.forceDifference_compact`, and the V2 lifespan record's inherited `.regular`, `.referenceLifespan`, `.lifespan` | `.forceConvergence` provides the norm inequality at `q=1` or `q=2`; `.lifespan` gives equality to `T`, stronger than membership in the breakdown set |
| `:183-195`: replace `F_R` by `F_c` or `F_rd` with the same thresholds | `IsR41DForceClass Y := Y=forceClassR or Y=forceClassCompact or Y=forceClassRapid`, quantified by both fields | A single `Y` is threaded through the reference quantifier and `breakdownSetIn`; this prevents accidentally measuring density relative to one class while returning a witness in another |
| `:192,195`: the rapid-decay formulation highlights `a in S_sigma` | Both fields retain the theorem's `a in initialClassR`; `Y=forceClassRapid` therefore implies the highlighted Schwartz case once `initialClassSchwartz subset initialClassR` is supplied | Line 195 says Theorem 4.1 remains valid after replacing the force class; the extra sentence singles out `S_sigma` but does not retract the theorem's `X_R` quantifier |

## Choices forced by `Contracts.V1`

| Manuscript phrase | Choice in the draft | Why this exact choice |
|---|---|---|
| A spatial/space-time force | `Data.SpaceTimeField`, with time first | This is the registered physical field type used by every R42 family and by the force norms |
| `X_R` | `a in Data.initialClassR` | This combines registered `MemHInfty` and pointwise solenoidality; no new initial-data predicate is copied |
| `F_R`, `F_c`, `F_rd` | `Data.forceClassR`, `Data.forceClassCompact`, `Data.forceClassRapid` | The three are sets in the same carrier, so one `Y` can parameterize the relative statement and the same lifespan function applies |
| Relative density in `L^1_t H^s_x` | `forall g in Y, forall r : ENNReal, 0<r, exists f ... forceSobolevENormL1 s (f-g)<r` | This is the explicit form of `Data.RelativelyDense 1 s Y ...`; the contract norm uses the strongly measurable Bochner datum path on `(0,infinity)` and fails safe to `top` |
| Relative density in `L^2_t H^s_x` | The analogous formula with `forceSobolevENormL2` | It is the registered `q=2` norm, not a spatial `L^2` norm and not a finite-time norm |
| The singular-force set | `Data.breakdownSetIn Y`, not `breakdownSetR` or `breakdownSetRZero` | The theorem fixes general `a`, not zero, and the requested class parameter would be lost by `breakdownSetR` |
| `T_max(a,f)<=T` | The lifespan part of `f in breakdownSetIn Y nu a T` | `maximalLifespanR` is `ENNReal`-valued; the real horizon is therefore embedded as `ENNReal.ofReal T` |
| Reference regular beyond `T` in the insertion case | R42 V2's inherited `regular` and `referenceLifespan` fields | `RegularThrough` carries an actual classical solution past a horizon, while `referenceLifespan` supplies the strict `ENNReal` inequality needed to select a margin; merely having a solution at horizon `T` would not encode a positive margin |
| Inserted breakdown | R42 V2's inherited `lifespan` field | It states `maximalLifespanR nu a (force eps)=ENNReal.ofReal T` for the same family; the density result only needs `<=` |
| First-case witness | `g` itself, recorded as an implementation obligation in both docstrings | Its norm difference is zero and its assumed lifespan inequality puts it in `breakdownSetIn`; no R42 object is consumed in this branch |
| Radius type | `r : ENNReal` with `0 < r` | This matches `Data.RelativelyDense` and the `ENNReal`-valued force norms, avoiding `.toReal` and its behavior at `top` |

## Upstream gaps exposed by this draft

| ID | Missing registered object (exact shape needed) | Why R41D needs it | Suggested owner |
|---|---|---|---|
| G1 | An end-to-end R42 adapter: for `nu,T>0`, `a in initialClassR`, `MemForceR g`, and `RegularThrough nu a g T`, produce a packet and `L : Contracts.V2.InsertionLifespan.InsertionLifespanV2API nu P` with `L.family.a=a`, `L.family.g=g`, and `L.family.T=T` | The registered `insertionFamilyStatement` begins with an already chosen packet/scaling/reference tuple, and `insertionLifespanV2Statement` begins with an already chosen family. R41D starts only with `(a,g,T)` and must obtain the correctly identified one family before projecting convergence and lifespan | R42 assembly |
| G2 | `forall f, MemForceRapid f -> MemForceR f` (equivalently `forceClassRapid subset forceClassR`) | R42's registered lifespan record requires `MemForceR` of the reference even when R41D is instantiated at `Y=forceClassRapid` | D01 data/force-class layer, consumed by R45 |
| G3 | `forall g f, MemForceRapid g -> MemForceCompact (fun z => f z-g z) -> MemForceRapid f` | `InsertionFamilyAPI.forceDifference_compact` gives exactly the middle hypothesis; this closure is needed to return the inserted force to the relative rapid-decay ambient class | R45 (`cor:Rclasses`) |
| G4 | `initialClassSchwartz subset initialClassR` | It specializes the `X_R` density field to the `S_sigma` sentence at `04-whole-space.tex:192,195` without redoing the Schwartz-to-Sobolev and solenoidal bridge | D01 initial-data layer, consumed by R45 |

No new definition is required for either topology, breakdown, lifespan, or the
two thresholds: `Contracts.V1.Data` already contains faithful objects for all
of them. The gaps above concern proof-facing assembly and class preservation,
not the truth conditions of `RDensityAPI`.

No extra upstream result is needed for the compact-class preservation step:
the exact difference-shaped adapter was not found, but it is an elementary
local consequence of the registered
`DatumLemmasAPI.memForceCompact_add` and the pointwise identity
`f = g + (f - g)`.  Likewise the `F_R` case already has the exact registered
field `DatumLemmasAPI.memForceR_of_compact_difference`.

## Blindness compliance

I did not read, open, grep, or search for another R41D draft, any pre-existing
file under `research/R41D/`, any other worktree, or any R41D entry in
`research/section4/STATEMENTS.md`. The only `research/R41D/` files accessed are
the two deliverables created in this lane (and the report created at handoff).
