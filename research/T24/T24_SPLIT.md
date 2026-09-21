# T24 — proof-lane split (`prop:affine` / `prop:multiple` / `prop:conservative`, `paper/sections/03-torus.tex:668-740`)

Lead-facing, 2026-09-18. Three independent leaves, exactly as reconciled in `research/T24/Spec.lean`
(namespaces `BlowupDensity.T24.{Affine,Multiple,Conservative}`) — design `research/T24/RECONCILIATION.md`
§2-§4, `COMPARISON.md` "Proof dependencies". Targets:

* **T24a** `AffineVariationAPI {ν} (P : PacketAPI ν) (c) (r τ₀ τ₁) : Prop`, **13 fields** (`Spec.lean:1010-1116`)
  + `affineVariationStatement:1117` — **whole space** on the registered `I01.packet`; T14 vocabulary only.
* **T24b** `MultipleRegionsAPI {ν} (P : PacketImportAPI ν) (T) {N} (regionCenter regionRadius) : Type`,
  **30 fields** (`Spec.lean:1176-1333`) + `multipleRegionsStatement:1335` — torus, superposes `N` T15-rescaled packets.
* **T24c** `ConservativeForcingAPI : Prop`, **2 fields** (`Spec.lean:1382-1414`) + `conservativeForcingStatement:1416`
  — torus, `T11`-only.

Three future contract ids: `T24.affine_variation`, `T24.multiple_regions`, `T24.conservative_forcing`.
Size: **S** ≤ ~100 lines; **M** one self-contained lemma with a known proof; **L** a multi-file campaign.
Model: `codex-sol` = reuse/transport/algebra/bookkeeping; `Opus` = analytic core.

## 0. Ground rules

**Peeling rule (T11/T19).** Every unit ends in a `theorem` whose statement **is** a `Spec.lean` field of one
of the three structures verbatim, or a lemma directly consumed by one. A unit that cannot close from the tree
names **at most one** input hypothesis (written out, non-tautological, satisfiable at a nonzero packet /
nonzero solution, discharged by a named later unit or a registered API); **no** named input for the hard
analytic units. No silent weakening of a V1 field; an honest narrowing is a new named predicate + a V2 contract.

**`formalization/` cannot import `PacketAPI`/`PacketImportAPI` (T17 G3, T18 lead note `T18_SPLIT.md:51`).**
So both `Prop`/`Type` records that index on a packet must be **restated over raw packet fields** on the
canonical module, exactly as T14 did and as T15 U-CAN (lane 384, `Section3/T15/Scaling.lean`) already did for
`PlacementData`/`ScalingAPI`:
- **T24a** canonical `Section3/T24/Affine.lean` takes `U P F : VelocityField/PressureField`, `energyBound
  dissipationBound : ℝ` and the `I01.packet` clauses it uses as explicit hypotheses — `velocity_smooth` on
  `preSingularDomain`, `momentum` on `Ioo 0 1` (`Packet.lean:237`), `spatialDivergence = 0` on `Ico 0 1`
  (`:232`), `zero_initial_velocity` (`:228`), `SpeedUnboundedAtOne velocity` (`:145`), `CompactPositiveTimeSupport
  force` (`:134`), `force_smooth`, and `energyENorm 1 velocity < ⊤`. The **probe** (may import `Contracts.*`)
  converts from `AffineVariationAPI {ν} (P : PacketAPI ν) c r τ₀ τ₁` by feeding `P.velocity/pressure/force` and
  `P`'s clauses; the registered whole-space vocabulary (`navierStokesResidual:127`, `SpeedUnboundedAtOne:145`,
  `CompactPositiveTimeSupport:134`, `energyENorm` `Data.lean:475`) is used verbatim.
- **T24b** canonical `Section3/T24/Multiple.lean` threads the **canonical** T15 records (lane 384's raw-field
  `PlacementData`/`ScalingAPI`) per region; the probe converts to the Spec's `PacketImportAPI`-based spelling.

**Finding: T24b does NOT consume T18.** `prop:multiple` *constructs* its assembled solution as the explicit
finite sum of T15-rescaled components (`RECONCILIATION.md §4` ⑦⑧); it never inserts a nearby singular force,
so — unlike T19 (density) — there is **no `thm:insertion` (T18) gate**. Every T24b gate is a **T15** field.
The only registered inputs T24 consumes are `I01.packet` (`Contracts/V1/Packet.lean`, T24a),
`T01.packet_import` (`Contracts/V1/PacketImport.lean`, T24b `P`), `T01.torus_local_theory`
(`Contracts/V1/TorusLocalTheory.lean`: `ClassicalSolutionT:144`, `maximalLifespanT:200`; T24b/T24c), and the
T15 `ScalingAPI`/`PlacementData` (spec reconciled, **proofs in progress** `research/T15/T15_SPLIT.md`).

**Candidate reuse (`SECTION3_PLAN.md` T24 row: `ConservativeForce.lean`, `PeriodicNonpositiveForce.lean`).**
T24c is **close to already proved locally**: `formalization/NSFormalization/Paper1/ConservativeForce.lean:91`
`zero_of_negative_gradient_on_Ico` has **exactly** `zero_from_rest`'s hypotheses (`ContDiffOn` on
`Ico 0 S ×ˢ univ` for `u,p,φ`; `UnitSpatialPeriodsOn`; `div u = 0` on `Ioo`; `Source.residual ν u p = -∇φ`;
`u(0,·)=0`) and **exactly** its corrected conclusion `∀ t ∈ Ico 0 S, ∀ x, u(t,x)=0`. Two `rfl` bridges (already
proved in T11 U1, lane 308 `Section3/T11/FlowConversion.lean`): `UnitSpatialPeriodsOn ≡ IsPeriodicOn`
(`PeriodicData.lean:62`, `Iff.rfl`) and `Source.residual ≡ navierStokesResidual` (`Source/Insertion.lean:21`,
`rfl`). Same file: `:23 zero_of_conservative_residual`, `:61 zero_velocity_negative_potential_residual`
(the `f=-∇φ` identification), `:70 zero_of_negative_gradient_on_Icc`. `PeriodicNonpositiveForce.lean:65,73`
is negative-order force-norm transfer — not needed by T24 (T24b's `force_mem` is `forceClassT` closure under
finite sums, not a norm bound). Shape precedents only (no registered counterpart — `grep` of `contracts.json`
for affine/multiple/conservative returns nothing): `Contracts/V1/GridObservations.lean` `GridFamilyAPI` for the
T24b `Fin N` family; `Contracts/V1/ForceClasses.lean` `ForceClassesAPI.regularReference`.

## 1. Units

### T24c — conservative forcing (`Prop`, 2 fields), `T11`-only, unblocked today

- **Uc1 — `zero_from_rest`.** Target verbatim (`Spec.lean:1408-1414`): `∀ ν, 0<ν → ∀ T, 0<T → ∀ φ,
  PeriodicPotentialT φ → ∀ S : ClassicalSolutionT ν 0 (conservativeForceT φ) T, ∀ t ∈ Ico 0 T, ∀ x,
  S.velocity (t,x) = 0`. Route: apply `ConservativeForce.lean:91 zero_of_negative_gradient_on_Ico` with `u :=
  S.velocity`, `p := S.pressure`, `φ`; transfer `S.velocity_smooth`/`pressure_smooth` (`ContDiffOn` `Ico 0 T`),
  `S.velocity_periodic`/`pressure_periodic` and `φ`'s two `PeriodicPotentialT` clauses (`:1367`) through the two
  `rfl` bridges; `S.divergence`, `S.momentum` (= `conservativeForceT φ = -pressureGradient φ`, def `:1372`),
  `S.initial` (`a=0`). **S–M, codex-sol.** No named input (candidate is unconditional). Deps: — (bridges = T11 U1, done).
- **Uc2 — `potential_pairing`.** Target verbatim (`Spec.lean:1391-1406`): the Haar pairing `∫_{T³} torusLift
  (fun x ↦ ⟪-∇φ(t,x), S.velocity(t,x)⟫) ∂periodicTorusMeasure = 0` at every `t ∈ Ico 0 T`, under the same
  hypotheses. Route: torus integration by parts (`RECONCILIATION.md §4` ⑨ first half) — at `t=0` from `S.initial`
  (`u=0`); at `t ∈ Ioo 0 T` from `∫∇φ·u = -∫ φ (div u) = 0` via `S.divergence`, `S.velocity_periodic`, Haar
  integrability of smooth periodic lifts (⑩, shared with T20 §4) and `integral_torusLift` (`Paper1/TorusCube.lean:40`);
  the internal pairing of `zero_of_conservative_residual` (`ConservativeForce.lean:23`) is the scaffold to mine.
  **M, Opus** (hard analytic: torus IBP). No named input. Deps: —.
  **DONE (lane 395).** `formalization/NSFormalization/Section3/T24/PotentialPairing.lean` `potential_pairing`,
  axioms `[propext, Classical.choice, Quot.sound]`. Route landed: NO `t=0` split needed — the whole `t ∈ Ico 0 T`
  is handled uniformly by the vendor torus-IBP lemma `NavierStokes.PeriodicUniqueness.cubeIntegral_pressure_energy_zero`
  (`vendor/…/PeriodicUniqueness.lean:435`, the mined form of the `zero_of_conservative_residual` scaffold): after
  `integral_torusLift`, rewrite `⟪-∇φ,u⟫ = -⟪u,∇φ⟫` (`inner_neg_left`+`real_inner_comm`) and discharge
  `∫_{cube}⟪u,∇φ⟫=0` for div-free periodic `u`. Hypotheses come from `S.velocity_smooth`
  (`ContDiffOn.comp_contDiff` → spatial `ContDiff` at every slab time, incl. `t=0`), `S.velocity_periodic`,
  `S.divergence`, and `φ`'s two `PeriodicPotentialT` clauses. **No `0<ν` used** — the statement is pure IBP.
  `PeriodicPotentialT`/`conservativeForceT` restated verbatim (lane 392 `Conservative.lean` not on base; dedupe in Uc3).
- **Uc3 — assembly + registration.** **DONE (lane 420).** Assemble `ConservativeForcingAPI` from Uc1+Uc2; `conservativeForcingStatement`
  is the alias (`:1416`), inhabited by the same two proofs. Register `T24.conservative_forcing` v1 (contract +
  binding + tests), `ClassicalSolutionT` structure exception as in `T01.torus_local_theory`. Non-vacuity: the rest
  solution at `φ=0` (`conservativeForceT 0 = 0`, zero `ClassicalSolutionT`) satisfies the hypotheses. Record the
  bounded-domain/no-slip omission (out of V1 scope) in the contract `scope`. **S–M, codex-sol.** Deps: Uc1, Uc2.
  Landed as `Section3/T24/ConservativeAssembly.lean`, with the two canonical fields assembled unconditionally and
  a viscosity-generic zero-velocity/zero-pressure `restSolution`.  Its Sobolev field reuses T11's genuine
  `constantVelocitySolutionT 0`; the binding uses `TorusLocalTheory.ofContract`/`toContract` fieldwise, and the
  registered test instantiates the actual contract solution at `φ=0`.  Axiom audit: exactly
  `[propext, Classical.choice, Quot.sound]`; no named input.

### T24a — affine variations (`Prop`, 13 fields), whole space / T14 only, unblocked today

- **Ua1 — geometry + kinematics** (`radius_pos:1014`, `window:1019`, `zero_initial:1055`, `late_agreement:1061`,
  `distinct:1091`). Route: `radius_pos`/`window` are the parameter hypotheses of `affineVariationStatement`;
  `zero_initial` from `U(0,·)=0` (raw `zero_initial_velocity`) + `b(0,·)=0` (`tsupport b ⊆ Ioo τ₀ τ₁ ×ˢ ball`,
  `τ₀>0`); `late_agreement` from `b=0` for `t ≥ τ₁`; `distinct` is `add_right_injective` on `affineVelocity`.
  **S, codex-sol.** No named input. Deps: —.
- **Ua2 — `divergence_free`** (`:1038`): `∀ b admissible, ∀ t ∈ Ico 0 1, ∀ x, spatialDivergence (U+b) t x = 0`. **Done (lane 402).**
  Route: additivity of `spatialDivergence` (⑦-algebra) from raw `∇·U=0` on `Ico 0 1` and `∇·b=0` (admissible,
  `AffineAdmissible:968`). **S–M, codex-sol.** No named input. Deps: —.
- **Ua3 — `momentum` (`eq:affine` expansion ①).** Target verbatim (`:1047`): `∀ b admissible, ∀ t ∈ Ioo 0 1,
  ∀ x, navierStokesResidual ν (affineVelocity U b) (affinePressure P) t x = affineForce ν U F b (t,x)`. Route:
  the six-term expansion `residual ν (U+b) P = (residual ν U P) + ∂ₜb − νΔb + (U·∇)b + (b·∇)U + (b·∇)b` from
  bilinearity of `spatialDerivative`/`advection` and linearity of `temporalDerivative`/`spatialLaplacian`/
  `pressureGradient`; then raw `momentum` (`residual ν U P = F` on `Ioo 0 1`) closes it against `affineForce:988`.
  **DONE (lane 398, Opus).** `formalization/NSFormalization/Section3/T24/AffineMomentum.lean`:
  `momentum` (raw-field, hyps = `velocity_smooth` + `navier_stokes` only; no named input, no pressure smoothness)
  + `navierStokesResidual_affine_expand` (the six-term expansion). Reused vendored `NavierStokes.ResidualCalculus`
  add-lemmas + interior-smoothness helpers rather than reproving bilinearity. Probe
  `research/T24/probes/affine_momentum_closes.lean` closes the registered field on `Bindings.packet ν hν`; both
  module theorems + all probe decls print `[propext, Classical.choice, Quot.sound]`. Imports the T24a affine
  vocabulary from lane 392 `AffineBasics.lean` (`import NSFormalization.Section3.T24.AffineBasics`; 392's defs are
  defeq to `Spec.lean`'s after the `VelocityField`/`SpaceTimeField` alias). Non-vacuity: probe
  `affine_momentum_nonzero.lean` builds a **nonzero** admissible `b = spatialCurl(θ·φ·e₁)` on `ball 0 1 × (1/4,3/4)`
  (`bWitness_admissible`, `bWitness_ne_zero`, `nonzero_admissible_momentum`, all standard-3 axioms); `closes.lean`
  covers `b=0` admissibility + `b=0`⇒packet-PDE reduction. **L, Opus** (hard analytic core). No named input. Deps: —.
- **Ua4 — `force_smooth` + `force_support` (smooth zero-extension across `t=1`, ②).** Targets verbatim
  (`:1025`, `:1032`): `ContDiff ℝ ∞ (affineForce …)` and `CompactPositiveTimeSupport (affineForce …)`. Route:
  every correction term is supported in `tsupport b`, a compact subset of `Ioo τ₀ τ₁ ×ˢ ball` with `τ₁<1`, on a
  neighborhood of which `U` (raw `velocity_smooth` on `preSingularDomain`) has bounded derivatives of every fixed
  order; so `(U·∇)b`, `(b·∇)U`, `(b·∇)b`, `∂ₜb`, `Δb` extend smoothly by zero across `t=1` and `F` is globally
  smooth with compact positive-time support (raw `force_smooth`/`force_support`). **L, Opus.** No named input. Deps: —.
  **DONE (lane 414, Opus).** `formalization/NSFormalization/Section3/T24/AffineForce.lean`:
  `force_smooth` (hyps = raw `velocity_smooth` + raw `force_smooth`, plus the parameter
  hypotheses `0 < τ₀`, `τ₁ < 1`) and `force_support` (hyp = raw `force_support`, plus `0 < τ₀`
  **only** — `τ₁ < 1` is genuinely unused there), with the reusable pieces
  `affineForce_eq_of_notMem_tsupport`, `contDiffOn_affineForce_interior`,
  `tsupport_affineForce_subset`, `affineCylinder_subset_interior`,
  `affineCylinder_subset_positiveTimeDomain`.  No named input, no `0 < ν`, no pressure.
  Route landed: the two-open-set gluing of the brief, with the analytic work taken
  wholesale from the **vendored** `NavierStokes.ResidualRegularity` (not `ResidualCalculus`):
  `contDiffOn_{temporalDerivative,spatialDerivative,spatialLaplacian}` on the open slab
  `Ioo 0 1 ×ˢ univ ⊆ preSingularDomain` (`preSingularDomain` itself is not open, so
  `0 < τ₀` is needed for *smoothness*, not only for positive time), and the locality
  lemmas `*_congr` (hypothesis `b =ᶠ[𝓝 z] 0` only) off `tsupport b`;
  `contDiff_iff_contDiffAt` + `ContDiffAt.congr_of_eventuallyEq` glue.  `force_support`
  avoids `HasCompactSupport.add` and any new definition: the single inclusion
  `tsupport (affineForce ν U F b) ⊆ tsupport F ∪ tsupport b` yields both halves.
  `τ₁ < 1` is carried **explicitly** (as lane 403 did): `AffineAdmissible` is satisfiable
  with `τ₁ ≥ 1` (take `b = 0`), so it cannot supply it.  Probes:
  `research/T24/probes/affine_force_closes.lean` discharges both registered fields on
  `Bindings.packet ν hν` in Contracts vocabulary and gives the `b = 0` reduction to the
  packet's own `force_smooth`/`force_support`;
  `research/T24/probes/affine_force_nonzero.lean` rebuilds lane 398's nonzero
  `bWitness = spatialCurl (θ·φ·e₁)` on `ball 0 1 × (1/4,3/4)` and instantiates both
  conclusions at it.  All module and probe declarations print
  `[propext, Classical.choice, Quot.sound]` (`research/T24/axioms_ua4.lean`).
- **Ua5 — `speed_unbounded`** (`:1069`): `∀ b admissible, SpeedUnboundedAtOne (affineVelocity U b)`. Route:
  `U+b = U` on `t ≥ τ₁` (Ua1 `late_agreement`, `τ₁<1`), so the packet's `SpeedUnboundedAtOne U` (raw field,
  `Packet.lean:145`) transfers. **S–M, codex-sol.** No named input. Deps: Ua1. **Done: lane 403.**
- **Ua6 — `energy_finite` (finite energy/dissipation + triangle ③).** Target verbatim (`:1076`): `∀ b
  admissible, energyENorm 1 (affineVelocity U b) < ⊤`. Route: `b` compactly supported smooth ⟹ `energyENorm 1 b
  < ⊤` (bounded velocity + gradient on a compact set, finite time interval); raw `energyENorm 1 U < ⊤` (packet
  `U ∈ E_1`); triangle inequality for `energyEssSup + energyGradient` (`Data.lean:475`). **M–L, Opus.** No named
  input. Deps: —.
  **DONE (lane 407).** `formalization/NSFormalization/Section3/T24/AffineEnergy.lean` `energy_finite`
  (`{U : VelocityField} (c : Space) (r τ₀ τ₁ : ℝ) (henergy : energyENorm 1 U < ⊤) : ∀ b, AffineAdmissible c r τ₀ τ₁ b
  → energyENorm 1 (affineVelocity U b) < ⊤`), axioms `[propext, Classical.choice, Quot.sound]`. Route landed
  **without Minkowski**: `eLpNorm_add_le` needs `AEStronglyMeasurable` slices of `U`, which the raw clause
  `energyENorm 1 U < ⊤` does not carry, so both halves go through `(x+y)² ≤ 4x²+4y²` in `ℝ≥0∞` plus
  `lintegral_add_right` (only the *right*, i.e. `b`, summand must be measurable — free, `b` is smooth). Gradient
  additivity likewise needs no differentiability of `U`: a case split gives `‖∇(U+b)‖ₑ ≤ ‖∇U‖ₑ + ‖∇b‖ₑ`
  unconditionally, the non-differentiable branch collapsing `∇(U+b)` to the `fderiv` junk value `0`. `b`'s two
  uniform bounds come from `Continuous.bounded_above_of_compact_support` on `b` and on
  `fun z ↦ spatialDerivative b z.1 z.2` (continuous by `ContDiff.fderiv`, compactly supported because `fderiv`
  of a slice vanishes off `tsupport b`), and `setLIntegral_eq_of_support_subset` confines each slice integral to
  the compact `Prod.snd '' tsupport b`. Constants are crude (`4`, `3Cg²`) — only finiteness is claimed. **The
  whole-space `E_T` had no local restatement** (`Section3.T10.energyENormT` is the torus norm), so
  `energyEssSup`/`energyGradient`/`energyENorm` are restated verbatim from `Contracts/V1/Data.lean:444-476` in
  §1 of the module; `research/T24/probes/affine_energy_closes.lean` checks all four `rfl` bridges (including
  `spatialGradient`) and discharges the `Spec.lean:1076-1077` field on `Bindings.packet ν hν`.
  **Open for Ua9:** `Contracts.V1.PacketAPI` has no `energyENorm 1 velocity < ⊤` field — it carries
  `energy_isLUB` (`Packet.lean:255`) and `dissipation_integrable`/`dissipation_eq` (`:260,266`) instead — so the
  probe threads the clause as a hypothesis. Assembling `‖U‖_{E_1} < ∞` from those three fields is a separate
  unit (route: `I02.eLpNorm_two_eq_ofReal_sqrt` + `energy_isLUB` for the `L^∞_tL²_x` half,
  `I03.eLpNorm_spatialGradient_sq_slice` + `dissipation_integrable` for the other), not Ua6.
- **Ua7 — `infinite_dimensional` (bump/curl library + independence ④).** Target verbatim (`:1085`): `∃ b : ℕ →
  SpaceTimeField, (∀ n, AffineAdmissible c r τ₀ τ₁ (b n)) ∧ LinearIndependent ℝ b`. Route: countably many
  disjoint balls in `ball c r`; in each a smooth compactly supported vector potential with nonzero curl, times a
  fixed nonzero time bump in `Ioo τ₀ τ₁`; the curls are div-free with disjoint spatial supports ⟹ `LinearIndependent`.
  Needs a bump-function library (no local precedent). **L, Opus.** No named input. Deps: —.
  **Single-bump witness now exists** (lane 398, `research/T24/probes/affine_momentum_nonzero.lean`):
  `bWitness := spatialCurl(θ·φ·e₁)` with `θ,φ : ContDiffBump`, proved smooth / compactly supported in the cylinder /
  divergence-free (`spatialDivergence_spatialCurl`) / nonzero (curl `e₂`-component `= ∂₃φ`, forced `≢0` by compact
  support). Ua7 lifts this to a countable disjoint-ball family + `LinearIndependent`.
  **DONE (lane 417, Opus).** Two new modules. `formalization/NSFormalization/Section3/T24/AffineWitness.lean` is
  the promoted, parameterised single-bump library (`AffineWitness.potential θ φ = (θ(t)·φ(x))•e₁`,
  `curlBump θ φ = spatialCurl (potential θ φ)`, `carrier θ φ = closedBall t₀ θ.rOut ×ˢ closedBall x₀ φ.rOut`)
  with `curlBump_contDiff` / `_hasCompactSupport` / `tsupport_curlBump_subset` / `_divergence_free` /
  `_eq_zero_of_notMem` / `curlBump_admissible` / `curlBump_ne_zero`; lane 398's `bWitness` is its instance
  `t₀=1/2, x₀=0, θ=⟨1/16,1/8⟩, φ=⟨1/2,3/4⟩` (the 398 probe was not edited).
  `formalization/NSFormalization/Section3/T24/AffineFamily.lean` carries the geometry
  (`scale n = 2⁻ⁿ`, `centerOffset r n = r·2⁻ⁿ/2`, `ballRadius r n = r·2⁻ⁿ/16`,
  `center c r n = c + centerOffset r n • e₁`), the two arithmetic facts
  `closedBall_subset_ball` (`⊆ ball c r`) and `radius_add_lt` (pairwise disjointness), the family
  `bFam c r τ₀ τ₁ hr hτ n = curlBump (timeBump τ₀ τ₁ hτ) (spaceBump c r hr n)`, and
  `theorem infinite_dimensional (c : Space) (r τ₀ τ₁ : ℝ) (hr : 0 < r) (hτ : τ₀ < τ₁) :
  ∃ b : ℕ → VelocityField, (∀ n : ℕ, AffineAdmissible c r τ₀ τ₁ (b n)) ∧ LinearIndependent ℝ b`.
  Hypotheses are only the two nondegeneracy facts `0 < r`, `τ₀ < τ₁` (`0 < τ₀` and `τ₁ < 1` from
  `AffineBasics.window` are not used); no named input, no packet clause. Independence is
  `linearIndependent_iff'` + disjoint supports: `curlBump_ne_zero` gives a point `z` with `b n z ≠ 0`, that `z`
  lies in `carrier`, so `z.2` is in the `n`-th ball and outside every other one, so all other terms of a vanishing
  finite combination die at `z`. Probe `research/T24/probes/affine_family_closes.lean` (registered vocabulary,
  `rfl` bridges, the field in both the `VelocityField` and the `SpaceTimeField` spelling, the packet-level
  strengthening `Function.Injective (n ↦ U + b n)` on `Bindings.packet ν hν` via `AffineBasics.distinct`,
  `b 0 ≠ b 1`, and two degeneracy checks showing `0 < r` / `τ₀ < τ₁` are load-bearing); audit
  `research/T24/axioms_ua7.lean` — all 42 declarations `[propext, Classical.choice, Quot.sound]`.
- **Ua8 — `nonisolated` (`C^m` bound ⑤).** Target verbatim (`:1104`): `∀ b admissible, b ≠ 0, ∀ m, Tendsto (fun
  λ ↦ ckSeminormE (tsupport b) m (Ũ_{λb}−U)) (𝓝 0) (𝓝 0) ∧ Tendsto (… F̃_{λb}−F …) (𝓝 0) (𝓝 0)`. Route:
  velocity difference `= λ • b`; force difference `= λ L_U b + λ²(b·∇)b` (reuse Ua3's expansion); on `tsupport b`
  all coefficients/derivatives are bounded, so `ckSeminormE (tsupport b) m ≤ C_m|λ| + C_m'λ²` (an `ℝ≥0∞` `⨆`,
  never the real `sSup` junk `0`), giving `Tendsto … (𝓝 0)`. **L, Opus.** No named input. Deps: Ua3.
  **DONE (lane 424).** `formalization/NSFormalization/Section3/T24/AffineNonisolated.lean` `nonisolated`
  (`{ν} {U F : VelocityField} (c r τ₀ τ₁) (hτ₀ : 0 < τ₀) (hτ₁ : τ₁ < 1)
  (hvelocity_smooth : ContDiffOn ℝ ∞ U preSingularDomain)`), axioms `[propext, Classical.choice, Quot.sound]`.
  Hypotheses consumed: **only** `velocity_smooth` + the two cylinder bounds — the packet's `force_smooth`
  is *not* needed (the ambient `F` cancels in the difference), nor `0 < ν`, nor the pressure, nor `b ≠ 0`
  (carried in the statement, unused in the proof). Route landed **not** with the paper's literal
  `λ L_U b + λ²(b·∇)b`: `L_U b` is not globally `ContDiff` (`U` is smooth only on `preSingularDomain`),
  so the difference is regrouped as `λ·(F̃_b − F) + (λ²−λ)·(b·∇)b`, whose two coefficient fields **are**
  globally smooth — `F̃_b − F = affineForce ν U 0 b` is lane 414's `force_smooth` at the **zero** force,
  and `(b·∇)b = advection b` is the vendored `contDiffOn_advection` on `univ`. That lets the global
  `fun_iteratedFDeriv_add_apply` / `iteratedFDeriv_const_smul_apply'` apply unchanged. Three new
  seminorm lemmas (none were in the tree): `affineCkSeminorm_const_smul` (exact homogeneity, with
  `ENNReal.mul_iSup` pushed through both binders of `⨆ z ∈ K`), `affineCkSeminorm_add_le`,
  `affineCkSeminorm_lt_top` (`ContDiff.continuous_iteratedFDeriv` +
  `IsCompact.exists_bound_of_continuousOn`) — the last is the brief's
  `ckSeminorm_lt_top_of_contDiff_compact`. Scalar linearity of the operators is the vendored
  `NavierStokes.ResidualCalculus` (`spatialDerivative_const_smul`, `spatialLaplacian_const_smul`);
  `(b·∇)U` needs no differentiability of `U` at all (`map_smul`). Probe
  `research/T24/probes/affine_nonisolated_closes.lean`: six `rfl` bridges (incl.
  `ckSeminormE ≡ affineCkSeminorm` and `SpaceTimeField ≡ VelocityField`), the field discharged on
  `Bindings.packet ν hν`, lane 398's nonzero `bWitness` rebuilt (lane 417's shared
  `Section3/T24/AffineWitness.lean` is not on this base) with both limits instantiated at it, and
  `nonisolated_nontrivial` — at `λ = 1`, `m = 0` the velocity seminorm of the nonzero witness is
  **nonzero**, so the limits are not limits of the zero function. Audit `research/T24/axioms_ua8.lean`;
  attempts/negative record `research/T24/ATTEMPTS_UA8.md`.
- **Ua9 — assembly + `affineVariationStatement` + registration + probe.** Assemble the 13 fields into
  `AffineVariationAPI`; `affineVariationStatement:1117` `Nonempty` from any `PacketAPI ν` (the registered
  `I01.packet` witness); the raw-field→`PacketAPI` probe (§0). Register `T24.affine_variation` v1; non-vacuity at
  `b=0` (admissible) and the full family. **M, codex-sol.** Deps: all Ua.
  **DONE (lane 430, Opus).** Registered as **`T04.affine_variation`** v1 (parent task `T04`, per the T24 work
  item — not `T24.*`), 43rd contract. Four files:
  `formalization/NSFormalization/Section3/T24/AffineAssembly.lean` (canonical: `AffineRawData` = the eight raw
  packet clauses the units consume, `AffineVariationCanonical` = the 13 Spec fields over raw `U P F`,
  `affineVariationCanonical` = thirteen one-line field assignments to lanes 392/398/402/403/407/414/417/424);
  `verification/Contracts/V1/AffineVariation.lean` (`Spec.lean:958-1121` copied token-for-token, only the
  namespace changed to `BlowupDensity.Contracts.V1`; imports `Contracts.V1.{Data,Packet}` only);
  `verification/Bindings/AffineVariation.lean` (seven whole-function `rfl` bridges — `affineCylinder`,
  `AffineAdmissible`, `crossAdvection`, `affineVelocity`, `affinePressure`, `affineForce`,
  `ckSeminormE ≡ affineCkSeminorm` — plus `packetRawData`, `affineVariation` for **any** `P : PacketAPI ν`,
  `affineVariationPacket` at `Bindings.packet ν hν`, `affineVariationStatement_holds`);
  `verification/Tests/AffineVariation.lean` (`checkedAffineVariation`, `checkedAffineVariationStatement`, both
  `run_cmd TestSupport.checkAxioms`; three field-shape conformance examples; non-vacuity at `b = 0` and at the
  nonzero `AffineWitness.curlBump` on `ball 0 1 × (1/4,3/4)`).
  **The Ua6 open gap is closed here**: `Section3.T24.energyENorm_lt_top_of_packet` derives
  `energyENorm 1 U < ⊤` — which `PacketAPI` does *not* carry — from `square_integrable` + `energy_isLUB`
  (`I02.eLpNorm_two_eq_ofReal_sqrt`, `essSup_le_of_ae_le`) and from `velocity_smooth` + `carrier_compact` +
  `velocity_support` + `dissipation_integrable` (`I03.eLpNorm_spatialGradient_sq_slice`,
  `ofReal_integral_eq_lintegral_ofReal`), exactly the route sketched in `ATTEMPTS_UA6.md`. All declarations
  print `[propext, Classical.choice, Quot.sound]` (`research/T24/axioms_ua9.lean`); attempts/negative record
  `research/T24/ATTEMPTS_UA9.md`. **T24a is complete**; T24b and T24c remain.

### T24b — multiple regions (`Type`, 30 fields), torus, **T15-gated** (no T18)

`sc j := (scaling j)` = the region-`j` T15 `ScalingAPI`; every field below is a conditional lemma over the
threaded canonical T15 records (draftable now), whose **instantiation / `Nonempty` closure waits on T15**.

**Lane 467 (2026-09-19): U-CAN DONE.** `Section3/T24/Multiple.lean` is the
canonical 30-field raw-packet `MultipleRegionsAPI` and full-clause
`multipleRegionsStatement`. The probe `probes/multiple_api_on_canonical.lean`
checks both fieldwise conversions and all 30 Spec projections.
**Ub1 DONE:** `MultipleComponents.lean`, `RegionsData.placement`,
`placement_time`, `placement_chart`, `scaling`, `ε`, `eps_admissible`, `eps_time`;
prescribed balls and horizon, radius-dependent threshold, no named input.
**Ub2 DONE:** `RegionsData.component` and `component_pin` select T15's solution.
**Ub3 DONE:** `RegionsData.component_support` and `component_force_support`;
velocity on `Ico 0 T`, force at every time, both on `fundamentalCube`.
T15 gates below are historical and are discharged by lane 459. No T18 is used.
Audit and exact resolved diagnostics: `axioms_ub1_ub3.lean`,
`ATTEMPTS_UB1_UB3.md`; report `REPORT_467.md`. Ub4–Ub7 remain future work.

- **Ub1 — placement + scaling selection** (`placement:1203`, `placement_time:1207`, `placement_chart:1213`,
  `scaling:1220`, `ε`, `eps_admissible:1226`, `eps_time:1230`). Route: for each `j`, build a `PlacementData` with
  `chartCenter = regionCenter j`, `chartRadius = regionRadius j` (`chartBall_in_cube` from `region_interior:1191`),
  `T := T`, and pick `ε_j ∈ Ioc 0 ε₀` with `ε_j² < T` (`eps_time`, `place.eps_le_one`); supply `ScalingAPI` for it.
  **M, codex-sol.** Named input: T15 `PlacementData`/`ScalingAPI` construction with prescribed chart ball
  (**blocked on T15 U2 `Placement.lean` + T15 U15 assembly `Nonempty`**). Deps: —.
- **Ub2 — components** (`component:1235`, `component_pin:1242`). Route: `sc j`.`solution (ε j)` gives
  `∃ S : ClassicalSolutionT ν 0 F_{ε_j} T, S.velocity = periodizedScaledVelocity … ∧ S.pressure =
  normalizedScaledPressure …`; select `S` and read off `component_pin`. **S–M, codex-sol.** Named input: T15
  `ScalingAPI.solution` (**blocked on T15 U11 `Solution.lean`**). Deps: Ub1.
- **Ub3 — single-copy supports** (`component_support:1252`, `component_force_support:1260`, ⑥). Route: on
  `fundamentalCube`, `sc j`.`velocity_singleCopy`/`force_singleCopy` reduce the periodization to one copy, and
  `place.eps_space` + `placement_chart:1213` put `x₀ + ε•K_*` inside `B_j`, so both vanish for `x ∈ Q ∖ B_j`.
  **M, codex-sol.** Named input: T15 `*_singleCopy` + `eps_space` (**blocked on T15 U3 `SingleCopy.lean` + U2**).
  Deps: Ub1, Ub2.
- **Ub4 — assembled solution** (`assembled_velocity/pressure/force` + three formulas `:1264-1285`,
  `solution:1287`, `solution_pin:1291`, `force_mem:1295`, `rest:1299`, ⑦). Route: `assembled_* :=` the explicit
  `finiteVelocitySum/PressureSum/ForceSum` (`:1144`, definitional). Disjoint supports (Ub3 + `regions_disjoint:1196`)
  kill every cross transport `(U_i·∇)U_j = 0`, so the sum solves `ClassicalSolutionT ν 0 (Σ F_j) T`; `forceClassT`
  and the zero-mean gauge are closed under finite sums (`force_mem`); `rest` from each `component`.`initial`.
  **L, Opus** (hard analytic core). No named input beyond the threaded `sc j`/components (Ub2, Ub3). Deps: Ub2, Ub3.
  **DONE (lane 468).** `MultipleAssembled.lean` constructs the explicit sums and actual `solution`,
  proves `crossTransport_eq_zero`, `solution_pin`, `force_mem`, and `rest`; all 29 declarations have
  exactly `[propext, Classical.choice, Quot.sound]`. Probe: `probes/assembled_closes.lean`;
  audit: `axioms_ub4.lean`; diagnostics: `ATTEMPTS_UB4.md`; report: `REPORT_468.md`.
- **Ub5 — region agreement + blow-up** (`region_agreement:1305`, `region_blowup:1313`). Route: on `B_j` every
  other component vanishes (Ub3, disjoint), so `assembled = component j` there; then `sc j`.`unboundedSpeed`
  transfers to `SpeedUnboundedAtOn T B_j assembled_velocity`. **M, codex-sol.** Named input: T15 `unboundedSpeed`
  (**blocked on T15 U6 `Blowup.lean`**). Deps: Ub3, Ub4.
  **DONE (lane 469).** `MultipleRegions.lean`: `RegionsData.region_agreement` and
  `region_blowup` for the explicit finite sum; no Ub4 dependency. T15's global
  blow-up construction is localized using scaled support before single-copy transfer.
- **Ub6 — energy + dissipation bounds** (`energy_bound:1321` `≤`, `dissipation_bound:1328` `=`, ⑧). Route:
  disjoint-support additivity `‖u(t)‖₂² = Σ‖U_j(t)‖₂²` and `∫‖∇u‖² = Σ∫‖∇U_j‖²` (Ub3), then `sc j`.
  `packetEnergyIdentity` (`= ε_j^{1/2}M`) gives `energyEssSupT² ≤ M²Σε_j` and `packetDissipationIdentity`
  (`= ε_j^{1/2}D`) gives `energyGradientT² = D²Σε_j` (equality, by disjointness). **L, Opus.** Named input: T15
  `packetEnergyIdentity`/`packetDissipationIdentity` (**blocked on T15 U4 `Energy.lean`**). Deps: Ub3.
  **DONE (lane 469).** `MultipleRegions.lean`: `RegionsData.energy_bound` (`≤`)
  and `dissipation_bound` (`=`), with exactly the original packet constants.
  Squared slice norms add by disjointness; gradients are localized on the cube
  interior and its null boundary removed. All 15 declarations have exactly
  `[propext, Classical.choice, Quot.sound]`; four exact field probes close.
- **Ub7 — assembly + `multipleRegionsStatement` + registration + non-vacuity.** Assemble the 30 fields;
  `multipleRegionsStatement:1335` `Nonempty` from the per-region T15 witnesses; probe to the `PacketImportAPI`
  spelling. Register `T04.multiple_regions` v1; record the bounded-domain/no-slip omission in `scope`. Non-vacuity
  at `N=1`, one region. **M, codex-sol.** **Blocked on all T15 (U2/U4/U6/U11/U15) + U-CAN lane 384.** Deps: all Ub.
  **DONE (lane 471).** `MultipleAssembly.lean` assembles all 30 canonical fields and proves the raw universal
  statement; the fieldwise binding registers `T04.multiple_regions`. The concrete registered `N=1`, `T=1`,
  radius-`1/4` centre-ball probe reads `region_blowup 0`. The bounded-domain/no-slip branch remains explicitly
  outside V1 scope.

## 2. Proof-dependency ledger (registered / threaded input each unit consumes)

| unit | leaf | `RECONCILIATION §4` lemma | registered / threaded input | gated on |
|---|---|---|---|---|
| Uc1 | conservative | — (candidate) | `ConservativeForce.lean:91`; T11 U1 bridges | no |
| Uc2 | conservative | ⑨(a) | `integral_torusLift`; ⑩ | no |
| Uc3 | conservative | — | `T01.torus_local_theory` | no |
| Ua1,Ua2 | affine | ⑦ | raw `I01.packet` clauses | no |
| Ua3 | affine | ① | raw `momentum` (`Packet.lean:237`) | no |
| Ua4 | affine | ② | raw `velocity_smooth`/`force_smooth` | no |
| Ua5 | affine | — | raw `SpeedUnboundedAtOne` (`:145`) | no |
| Ua6 | affine | ③ | raw `energyENorm 1 U < ⊤` | no |
| Ua7 | affine | ④ | bump-function library (new) | no |  <!-- done: lane 417 -->
| Ua8 | affine | ⑤ | Ua3 expansion | no |
| Ua9 | affine | — | `I01.packet` (contract) | no |  <!-- done: lane 430, `T04.affine_variation` -->
| Ub1 | multiple | — | T15 `PlacementData`/`ScalingAPI` | done, lane 467 |
| Ub2 | multiple | — | T15 `ScalingAPI.solution` | done, lane 467 |
| Ub3 | multiple | ⑥ | T15 `*_singleCopy` + `eps_space` | done, lane 467 |
| Ub4 | multiple | ⑦ | threaded components (Ub2,Ub3) | (via Ub2/Ub3) |
| Ub5 | multiple | — | T15 `unboundedSpeed` | **T15 U6** |
| Ub6 | multiple | ⑧ | T15 `packet{Energy,Dissipation}Identity` | **T15 U4** |
| Ub7 | multiple | — | all T15 + U-CAN 384 | done, lane 471 |

No T18 anywhere: T24b superposes T15 outputs, it does not insert.

## 3. Waves (≤ 3 concurrent; conservative + unblocked affine first, T15-gated multiple last)

| wave | units | sizes / models | status |
|---|---|---|---|
| W1 | **Uc1** zero_from_rest · **Uc2** potential_pairing · **Ua1** geometry/kinematics | S–M sol / M Opus / S sol | **Uc1 + Ua1 done (lane 392)**; Uc2 in progress |
| W2 | **Uc3** conservative assembly+register · **Ua2** divergence · **Ua3** momentum ① | S–M sol / S–M sol / L Opus | unblocked |
| W3 | **Ua4** force smooth-ext ② · **Ua5** speed_unbounded · **Ua6** energy_finite ③ | L Opus / S–M sol / M–L Opus | **Ua5 done (lane 403)**; Ua4/Ua6 unblocked |
| W4 | **Ua7** infinite_dim ④ · **Ua8** nonisolated ⑤ | L Opus / L Opus | unblocked |
| W5 | **Ua9** affine assembly+register · **Ub4** assembled solution ⑦\* · **Ub3** single-copy supports\* | M sol / L Opus / M sol | affine done; T24b conditional lemmas begin |
| W6 | **Ub1** placement/scaling\* · **Ub2** components\* · **Ub5** region agree/blowup\* · **Ub6** energy/dissip ⑧\* · **Ub7** multiple assembly+register\* | M sol / S–M sol / M sol / L Opus / M sol | **\* gated on T15 (U2/U3/U4/U6/U11/U15)** |

T24a is a fully unblocked whole-space campaign (W1-W5); T24c closes in W1-W2 off the registered `T11` +
`ConservativeForce.lean`. T24b's field lemmas (Ub3-Ub6) are draftable now as conditionals over the threaded
T15 records, but every instantiation and the `Nonempty` statement wait on T15's proofs.

## 4. Risks

1. **T24a `momentum`/`nonisolated` bilinearity (Ua3/Ua8).** The `eq:affine` six-term expansion must use the
   *registered* `spatialDerivative`/`advection` tokens; a mismatch with the packet's `navierStokesResidual`
   convection order silently breaks it. Check against `Packet.lean:127` before drafting.
2. **T24a `force_smooth` across `t=1` (Ua4).** The clause that makes the affine family honest: the correction is
   smooth at the singular time only because `tsupport b ⊆ Ioo τ₀ τ₁ ×ˢ ball` with `τ₁<1`. No lane may weaken
   `ContDiff ℝ ∞` (global) to `ContDiffOn` on `Ico 0 1`.
3. **T24a bump-function library (Ua7).** Countably many disjoint balls with div-free curls is new infrastructure
   (no local precedent); if it stalls, `infinite_dimensional` is the long pole of T24a. Cap the probe, mine
   Mathlib `ContDiffBump` + `Set.exists_seq_...` for the disjoint-ball selection.
4. **T24b is entirely T15-gated.** Nothing in T24b can register until T15 U15 (assembly `Nonempty`, itself
   blocked on T13.localization) lands. Draft Ub3-Ub6 as conditional lemmas over lane 384's canonical records to
   keep the critical path warm, but do not schedule Ub7 registration before T15/T13.
5. **Bounded-domain / no-slip branches** of `prop:multiple` (`:698,706,720`) and `prop:conservative` (`:724-725`)
   are omitted (no carrier in the tree); recorded in each contract `scope`, an open owner question
   (`COMPARISON.md` "Open questions" 2), not a placeholder field.

## Phase 5 P4 — lane 495

**Closed**: Proposition 3.17 bounded no-slip branch (`C317_B`).
`ConservativeOmega.lean` supplies direct boundary-IBP pairing, the normalized
`-φ` rest witness, and zero-from-rest via the energy identity. Potential class
is `ContDiff ℝ ∞ φ`, without periodicity or temporal support. Both branches are
registered by `T04.conservative_forcing_v2`; see `REPORT_495.md`.
## P5 units

**496 status:** bounded-domain specification only, in `SpecOmega.lean` and
canonical `Section3/T24/MultipleOmega.lean`. Thirty fields, with torus `scaling`
dropped and `no_slip` added; see `COMPARISON_OMEGA.md`. `M316_B` remains Partial.
The following are future proof units for lane 497, followed by registration 498.
No unit may take `MultipleRegionsOmegaAPI` or its existence as an input.

| Unit | Exact target fields | Supplier / required work |
|---|---|---|
| P5.1 placement and components on Ω | `T_pos`, `N_pos`, `regionRadius_pos`, `region_interior`, `regions_disjoint`, `placement`, `placement_time`, `placement_chart`, `ε`, `eps_admissible`, `eps_time`, `component`, `component_pin`, `component_support`, `component_force_support` | Raw packet hypotheses from `multipleRegionsOmegaStatement`; `T23.Placement.domainPlacementData` at each prescribed ball. T15.Bridges `scaledVelocity/scaledPressure/scaledForce` at `scaledStartTime T ε = T − ε²`; I03.Energy `scaled_smoothOn` and Source.PacketScaling `dilate_smoothOn`, `delayed_parabolic_divergence`, `delayed_parabolic_equation`, `delayed_full_support`, `delayed_pressure_support`, and `parabolicForce_support`. Prove neighborhood smoothness for velocity and pressure on `[0,T) × closure Ω`, initial vanishing, and support inside B_j. Use `T23.PressureNormalization` for the Ω gauge. No T23 background or correction. |
| P5.2 finite sum solution | `assembled_velocity`, `assembled_velocity_formula`, `assembled_pressure`, `assembled_pressure_formula`, `assembled_force`, `assembled_force_formula`, `solution`, `solution_pin`, `force_mem`, `rest`, `no_slip` | P5.1 plus finite sums, `T23.Triple.SmoothOnClosedSlab.add`, `MemForceOmega.add`, `domain_residual_add`, and `T23.PressureNormalization.domainNormalizePressure_integral`. Adapt `MultipleAssembled.crossTransport_eq_zero` to global disjoint supports; construct every `ClassicalSolutionOmega` field, including divergence, momentum, pressure gauge and frontier vanishing. |
| P5.3 per-ball singularity | `region_agreement`, `region_blowup` | P5.1–2 supports and disjointness; localize the raw scaled blow-up witnesses as in `MultipleRegions.lean` before its torus transfer. Source.PacketScaling `speed_unbounded_at_target`, `zeroPastField_speed` and the raw packet `SpeedUnboundedAtOne` supply separate time sequences. |
| P5.4 energy/dissipation additivity | `energy_bound`, `dissipation_bound` | P5.1 global supports: restricted integrals equal whole-space integrals for each component and its full gradient. I03.Energy `eLpNorm_scaled_slice`, `energyEssSup_scaled_le`, `scaled_total_dissipation`, `energyGradient_scaled_eq`; adapt finite disjoint-support square additivity from `MultipleRegions.lean`. Keep energy ≤ and dissipation = with the original M,D. No torus boundary-null-set argument is needed. |
| P5.5 assembly (497) and registration (498) | `multipleRegionsOmegaStatement`, every field of `MultipleRegionsOmegaAPI`; future `T04.multiple_regions_v2` | Assemble P5.1–4 from the raw hypotheses, then bind the reconciled research and canonical records fieldwise. Only after that add the V2 contract/binding/test and update M316_B, audits and coverage through the common closing procedure. Retain V1 torus registration. |

The unit-box, one-region probe is a type/elaboration check with an API variable,
not a proof of existence or a claimed non-vacuity witness. Proving that existence
is P5.5, not lane 496.

### Lane 500 P5b status

- **P5.3 CLOSED**: `NSFormalization.Section3.T24.OmegaRegions.region_agreement` and
  `region_blowup`, over explicit global support, disjointness, raw velocity pin,
  positive scales and time placement. Probe passes; both declarations use exactly
  `[propext, Classical.choice, Quot.sound]`. Assembly remains P5.5 (lane 501).
- **P5.4 CLOSED**: `NSFormalization.Section3.T24.OmegaRegions.energy_bound` and
  `dissipation_bound`; compact support identifies restricted Ω velocity/full-gradient
  norms with whole-space norms, disjoint supports give exact slice additivity,
  and I03 supplies the original M,D normalization. Energy is ≤; dissipation is =.
  Raw packet clauses are bundled only in the existing I03 `PacketData`; the probe
  constructs that bundle from the canonical raw hypotheses. No analytic residual.
**497 P5.1 DONE:** `MultipleOmegaComponents.lean`, `RegionsOmegaData` constructs
prescribed domain placements, admissible scales, actual gauged no-slip components
and global velocity/force support. No solution or target API premise. Module and
field probe elaborate without output; all 16 definitions/theorems have exactly
the three standard axioms (`axioms_p5a.lean`). P5.2 is in progress.

**497 P5.2 DONE:** `MultipleOmegaAssembled.lean` constructs the explicit finite
sums and `RegionsOmegaData.solution`, including cross-transport cancellation,
slab smoothness, domain gauge, force class, global rest and no-slip. All P5.1–2
fields are checked by `probes/p5a_closes.lean` using `exact`; all 45 module
names have exactly the standard three axioms. P5.3–5 and registration remain
with their assembly lanes; `M316_B` remains Partial.
### Lane 500 P5b status

- **P5.3 CLOSED**: `MultipleOmegaRegions.OmegaRegions.region_agreement` and
  `region_blowup`, over explicit global support, disjointness, raw velocity pin,
  positive scales and time placement. Probe passes; both declarations use exactly
  `[propext, Classical.choice, Quot.sound]`. Assembly remains P5.5 (lane 501).
- **P5.4 CLOSED**: `MultipleOmegaRegions.OmegaRegions.energy_bound` and
  `dissipation_bound`; compact support identifies restricted Ω velocity/full-gradient
  norms with whole-space norms, disjoint supports give exact slice additivity,
  and I03 supplies the original M,D normalization. Energy is ≤; dissipation is =.
  Raw packet clauses are bundled only in the existing I03 `PacketData`; the probe
  constructs that bundle from the canonical raw hypotheses. No analytic residual.

### Lane 501 P5.5 CLOSED

`MultipleOmegaAssembly.multipleRegionsOmegaAPI` constructs all thirty fields;
`multipleRegionsOmegaStatement_holds` supplies the raw universal statement.
P5b's hypotheses are discharged by P5a's actual components; the velocity sums
are definitionally equal, without deduplication. The registered unit-box,
N=1, ν=T=1 probe reads blow-up and no-slip from concrete inhabitants.
`T04.multiple_regions_v2` conjoins both branches of Proposition 3.16; V1 remains.
M316_B and the article row are Closed (22 Closed / 5 Partial). Full article
audit, make check/test/test-mutations/paper pass. See REPORT_501.md for the
four-part statement, file, diagnostic and command ledger.
