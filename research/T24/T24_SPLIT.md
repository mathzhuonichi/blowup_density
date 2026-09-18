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
- **Uc3 — assembly + registration.** Assemble `ConservativeForcingAPI` from Uc1+Uc2; `conservativeForcingStatement`
  is the alias (`:1416`), inhabited by the same two proofs. Register `T24.conservative_forcing` v1 (contract +
  binding + tests), `ClassicalSolutionT` structure exception as in `T01.torus_local_theory`. Non-vacuity: the rest
  solution at `φ=0` (`conservativeForceT 0 = 0`, zero `ClassicalSolutionT`) satisfies the hypotheses. Record the
  bounded-domain/no-slip omission (out of V1 scope) in the contract `scope`. **S–M, codex-sol.** Deps: Uc1, Uc2.

### T24a — affine variations (`Prop`, 13 fields), whole space / T14 only, unblocked today

- **Ua1 — geometry + kinematics** (`radius_pos:1014`, `window:1019`, `zero_initial:1055`, `late_agreement:1061`,
  `distinct:1091`). Route: `radius_pos`/`window` are the parameter hypotheses of `affineVariationStatement`;
  `zero_initial` from `U(0,·)=0` (raw `zero_initial_velocity`) + `b(0,·)=0` (`tsupport b ⊆ Ioo τ₀ τ₁ ×ˢ ball`,
  `τ₀>0`); `late_agreement` from `b=0` for `t ≥ τ₁`; `distinct` is `add_right_injective` on `affineVelocity`.
  **S, codex-sol.** No named input. Deps: —.
- **Ua2 — `divergence_free`** (`:1038`): `∀ b admissible, ∀ t ∈ Ico 0 1, ∀ x, spatialDivergence (U+b) t x = 0`.
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
  module theorems + all probe decls print `[propext, Classical.choice, Quot.sound]`. Restated the T24a affine
  vocabulary verbatim in-module (lane 392 `AffineBasics.lean` not on base; assembly dedupes). Nonzero-`b`
  non-vacuity deferred to Ua7 (curl-bump); probe covers `b=0` admissibility + `b=0`⇒packet-PDE reduction.
  **L, Opus** (hard analytic core). No named input. Deps: —.
- **Ua4 — `force_smooth` + `force_support` (smooth zero-extension across `t=1`, ②).** Targets verbatim
  (`:1025`, `:1032`): `ContDiff ℝ ∞ (affineForce …)` and `CompactPositiveTimeSupport (affineForce …)`. Route:
  every correction term is supported in `tsupport b`, a compact subset of `Ioo τ₀ τ₁ ×ˢ ball` with `τ₁<1`, on a
  neighborhood of which `U` (raw `velocity_smooth` on `preSingularDomain`) has bounded derivatives of every fixed
  order; so `(U·∇)b`, `(b·∇)U`, `(b·∇)b`, `∂ₜb`, `Δb` extend smoothly by zero across `t=1` and `F` is globally
  smooth with compact positive-time support (raw `force_smooth`/`force_support`). **L, Opus.** No named input. Deps: —.
- **Ua5 — `speed_unbounded`** (`:1069`): `∀ b admissible, SpeedUnboundedAtOne (affineVelocity U b)`. Route:
  `U+b = U` on `t ≥ τ₁` (Ua1 `late_agreement`, `τ₁<1`), so the packet's `SpeedUnboundedAtOne U` (raw field,
  `Packet.lean:145`) transfers. **S–M, codex-sol.** No named input. Deps: Ua1.
- **Ua6 — `energy_finite` (finite energy/dissipation + triangle ③).** Target verbatim (`:1076`): `∀ b
  admissible, energyENorm 1 (affineVelocity U b) < ⊤`. Route: `b` compactly supported smooth ⟹ `energyENorm 1 b
  < ⊤` (bounded velocity + gradient on a compact set, finite time interval); raw `energyENorm 1 U < ⊤` (packet
  `U ∈ E_1`); triangle inequality for `energyEssSup + energyGradient` (`Data.lean:475`). **M–L, Opus.** No named
  input. Deps: —.
- **Ua7 — `infinite_dimensional` (bump/curl library + independence ④).** Target verbatim (`:1085`): `∃ b : ℕ →
  SpaceTimeField, (∀ n, AffineAdmissible c r τ₀ τ₁ (b n)) ∧ LinearIndependent ℝ b`. Route: countably many
  disjoint balls in `ball c r`; in each a smooth compactly supported vector potential with nonzero curl, times a
  fixed nonzero time bump in `Ioo τ₀ τ₁`; the curls are div-free with disjoint spatial supports ⟹ `LinearIndependent`.
  Needs a bump-function library (no local precedent). **L, Opus.** No named input. Deps: —.
- **Ua8 — `nonisolated` (`C^m` bound ⑤).** Target verbatim (`:1104`): `∀ b admissible, b ≠ 0, ∀ m, Tendsto (fun
  λ ↦ ckSeminormE (tsupport b) m (Ũ_{λb}−U)) (𝓝 0) (𝓝 0) ∧ Tendsto (… F̃_{λb}−F …) (𝓝 0) (𝓝 0)`. Route:
  velocity difference `= λ • b`; force difference `= λ L_U b + λ²(b·∇)b` (reuse Ua3's expansion); on `tsupport b`
  all coefficients/derivatives are bounded, so `ckSeminormE (tsupport b) m ≤ C_m|λ| + C_m'λ²` (an `ℝ≥0∞` `⨆`,
  never the real `sSup` junk `0`), giving `Tendsto … (𝓝 0)`. **L, Opus.** No named input. Deps: Ua3.
- **Ua9 — assembly + `affineVariationStatement` + registration + probe.** Assemble the 13 fields into
  `AffineVariationAPI`; `affineVariationStatement:1117` `Nonempty` from any `PacketAPI ν` (the registered
  `I01.packet` witness); the raw-field→`PacketAPI` probe (§0). Register `T24.affine_variation` v1; non-vacuity at
  `b=0` (admissible) and the full family. **M, codex-sol.** Deps: all Ua.

### T24b — multiple regions (`Type`, 30 fields), torus, **T15-gated** (no T18)

`sc j := (scaling j)` = the region-`j` T15 `ScalingAPI`; every field below is a conditional lemma over the
threaded canonical T15 records (draftable now), whose **instantiation / `Nonempty` closure waits on T15**.

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
- **Ub5 — region agreement + blow-up** (`region_agreement:1305`, `region_blowup:1313`). Route: on `B_j` every
  other component vanishes (Ub3, disjoint), so `assembled = component j` there; then `sc j`.`unboundedSpeed`
  transfers to `SpeedUnboundedAtOn T B_j assembled_velocity`. **M, codex-sol.** Named input: T15 `unboundedSpeed`
  (**blocked on T15 U6 `Blowup.lean`**). Deps: Ub3, Ub4.
- **Ub6 — energy + dissipation bounds** (`energy_bound:1321` `≤`, `dissipation_bound:1328` `=`, ⑧). Route:
  disjoint-support additivity `‖u(t)‖₂² = Σ‖U_j(t)‖₂²` and `∫‖∇u‖² = Σ∫‖∇U_j‖²` (Ub3), then `sc j`.
  `packetEnergyIdentity` (`= ε_j^{1/2}M`) gives `energyEssSupT² ≤ M²Σε_j` and `packetDissipationIdentity`
  (`= ε_j^{1/2}D`) gives `energyGradientT² = D²Σε_j` (equality, by disjointness). **L, Opus.** Named input: T15
  `packetEnergyIdentity`/`packetDissipationIdentity` (**blocked on T15 U4 `Energy.lean`**). Deps: Ub3.
- **Ub7 — assembly + `multipleRegionsStatement` + registration + non-vacuity.** Assemble the 30 fields;
  `multipleRegionsStatement:1335` `Nonempty` from the per-region T15 witnesses; probe to the `PacketImportAPI`
  spelling. Register `T24.multiple_regions` v1; record the bounded-domain/no-slip omission in `scope`. Non-vacuity
  at `N=1`, one region. **M, codex-sol.** **Blocked on all T15 (U2/U4/U6/U11/U15) + U-CAN lane 384.** Deps: all Ub.

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
| Ua7 | affine | ④ | bump-function library (new) | no |
| Ua8 | affine | ⑤ | Ua3 expansion | no |
| Ua9 | affine | — | `I01.packet` (probe) | no |
| Ub1 | multiple | — | T15 `PlacementData`/`ScalingAPI` | **T15 U2, U15** |
| Ub2 | multiple | — | T15 `ScalingAPI.solution` | **T15 U11** |
| Ub3 | multiple | ⑥ | T15 `*_singleCopy` + `eps_space` | **T15 U3, U2** |
| Ub4 | multiple | ⑦ | threaded components (Ub2,Ub3) | (via Ub2/Ub3) |
| Ub5 | multiple | — | T15 `unboundedSpeed` | **T15 U6** |
| Ub6 | multiple | ⑧ | T15 `packet{Energy,Dissipation}Identity` | **T15 U4** |
| Ub7 | multiple | — | all T15 + U-CAN 384 | **T15 U2/U4/U6/U11/U15** |

No T18 anywhere: T24b superposes T15 outputs, it does not insert.

## 3. Waves (≤ 3 concurrent; conservative + unblocked affine first, T15-gated multiple last)

| wave | units | sizes / models | status |
|---|---|---|---|
| W1 | **Uc1** zero_from_rest · **Uc2** potential_pairing · **Ua1** geometry/kinematics | S–M sol / M Opus / S sol | unblocked (T11 registered) |
| W2 | **Uc3** conservative assembly+register · **Ua2** divergence · **Ua3** momentum ① | S–M sol / S–M sol / L Opus | unblocked |
| W3 | **Ua4** force smooth-ext ② · **Ua5** speed_unbounded · **Ua6** energy_finite ③ | L Opus / S–M sol / M–L Opus | unblocked |
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
