# T24 merged comparison — `prop:affine` / `prop:multiple` / `prop:conservative`

Reconciled spec: `research/T24/Spec.lean` (namespaces `BlowupDensity.T24.Affine`,
`.Multiple`, `.Conservative`).  Base draft **B** (lane 307); draft A (lane 306)
contributes only its clause enumeration (its 42 fields are bare `Prop`
placeholders, forbidden by `CLAUDE.md` 硬规矩 3).  Rulings are the lead's
`research/T24/RECONCILIATION.md`.  Paper source: `paper/sections/03-torus.tex:667-740`.

Vocabulary: everything registered (`Contracts.V1.{Data,Packet,TorusData,Scaling,HomogeneousNorm}`)
is imported.  The T10 solution class, T13 localization, T14 packet-import and T15
scaling vocabulary is copied verbatim (byte-for-byte identical to
`research/T15/Spec.lean:17-924`) into the namespaces `T10.Draft`, `T13.Spec`,
`T14.Draft`, `T15.Draft`.

## `prop:affine` — `AffineVariationAPI {ν} (P : PacketAPI ν) (c) (r τ₀ τ₁) : Prop` (13 fields)

Ambient space: **whole space** (`:669-671` fix the Theorem 1.1 packet and a
cylinder `B₀ ⋐ ℝ³`, terminal time `1`).  Indexed by the registered `PacketAPI`;
copies nothing from T10/T13/T15.

| Paper clause (`03-torus.tex`) | Lean field | A | B | ruling |
|---|---|---|---|---|
| `:670-671` cylinder `B₀×(τ₀,τ₁)`, `0<τ₀<τ₁<1`, `B₀` open ball | `radius_pos`, `window`; def `affineCylinder` | `cylinder`,`cylinder_hypotheses` (Prop) | data on torus, `τ₁<terminal` | **whole space, params.** `:671` writes `B₀⋐ℝ³`, `:670` `τ₁<1`; terminal `1`. |
| `:672-673` `b∈C_c^∞(Q)`, `∇·b=0` | def `AffineAdmissible` | `perturbation_class` | field (verbatim) | **B verbatim.** `HasCompactSupport` + closed `tsupport ⊆` open cylinder + pointwise `∇·b=0`. |
| `eq:affine :674-676` `Ũ=U+b`, `P̃=P`, six-term `F̃` | defs `affineVelocity`,`affinePressure`,`crossAdvection`,`affineForce` | `velocity/pressure/force_definition` | defs (verbatim) | **B verbatim**, registered `temporalDerivative`/`spatialLaplacian`/`spatialDerivative`, transport order preserved. |
| `:681-683` `F̃` smooth on all spacetime; compact support in `(0,∞)` | `force_smooth`, `force_support` | `support_away_endpoints`,`equation_and_divergence` | inside `family` | **split per clause**; `CompactPositiveTimeSupport` (registered). |
| `:673,679` `∇·(U+b)=0` on `[0,1)` | `divergence_free` | `equation_and_divergence` | inside `family` | split; on `Ico 0 1`. |
| `:674-676,679` momentum `= F̃` on `(0,1)` | `momentum` | `equation_and_divergence` | inside `family` | registered `navierStokesResidual`; genuine (uses `P`'s equation). |
| `:684-685` `Ũ(0,·)=0` | `zero_initial` | `zero_initial_data` | inside `family` | split. |
| `:684-685` `Ũ=U` for `t≥τ₁` | `late_agreement` | inside `family` | inside `family` | split. |
| `:686` same blow-up | `speed_unbounded` | `same_late_singularity` | inside `family` (`SpeedUnboundedAt`) | **`SpeedUnboundedAtOne`** (registered whole-space, terminal `1`). |
| `:686-687` finite energy & dissipation | `energy_finite` | `finite_energy_dissipation` | `energyENormT<⊤ ∧ energyGradientT<⊤` | **`energyENorm 1 < ⊤`** (registered whole-space); the second conjunct is implied. |
| `:688-691` infinite-dimensional independent family | `infinite_dimensional` | `infinite_dimensional` (Prop) | field | **B**: `∃ b:ℕ→…, (∀n admissible) ∧ LinearIndependent ℝ b`. |
| `:691` `b↦U+b` injective ⇒ distinct | `distinct` | (folded) | field | **B**. |
| `:677,692-696` non-isolation of the `λb` family in every `C^m` seminorm | def `ckSeminormE` + `nonisolated` | `nonisolated_scaling` (Prop) | `affineCkSeminorm` real `sSup` + `∀K` | **`ℝ≥0∞` `⨆`, `K=tsupport b`, `Tendsto` only**; the real `sSup` junk `0` would make it vacuous; drop the `∀K` and the quantitative `C_m|λ|+C_m'λ²`. |

Dropped from A (proof steps / already-in-solution-class): none applicable here
(A's affine fields are all bare `Prop`).  Dropped from B: `base` as a torus
`ClassicalSolutionT`, the free `terminal`, the `energyGradientT<⊤` conjunct, the
`∀K` support generality in `nonisolated`.

## `prop:multiple` — `MultipleRegionsAPI {ν} (P : PacketImportAPI ν) (T) {N} (regionCenter) (regionRadius) : Type` (30 fields)

Ambient space: torus.  `ν,T,N` and the balls are **parameters**.  `M,D` are
`P.energyBound`/`P.dissipationBound` (no new constants).

| Paper clause (`03-torus.tex`) | Lean field | A | B | ruling |
|---|---|---|---|---|
| `:698` `T>0`; `ν>0` | `T_pos` (`ν>0` from `P`) | `positive_*` (Prop) | data `ν,T`+`_pos` | **params**; `ν>0` inherited from `PacketImportAPI`. |
| `:697-700` `N` disjoint interior balls | `N_pos`,`regionRadius_pos`,`region_interior`,`regions_disjoint` | `region_count`,`disjoint_interior_regions` | data | **balls as params**; `region_interior` via `interior fundamentalCube`. |
| `:701-706` per-region placement, common `T`, chart ball `=B_j`, scaling, scale `ε_j` | `placement`,`placement_time`,`placement_chart`,`scaling`,`ε`,`eps_admissible`,`eps_time` | `scale_choice`,`separation_hypothesis` | data + `placement_center_mem`,`scaled_carrier_in_region` | **add `placement_chart`** (pins T15 chart ball to `B_j`); this makes `placement_center_mem`/`scaled_carrier_in_region` derivable — **dropped**. `ε_j²<T` kept (`:702`). |
| `:706-712` selected components pinned to T15 fields | `component`,`component_pin` | `simultaneous_solution` | fields | **B**. |
| `:701-712` component/force supports | `component_support`,`component_force_support` | `scaled_support_containment` | `tsupport ⊆ ball` (FALSE) | **measured on `fundamentalCube`**: periodized fields are unit-periodic, so their `ℝ³`-`tsupport` meets every lattice translate and is never inside one ball. Form matches T15's `velocity_singleCopy`/`force_singleCopy`+`eps_space`. |
| `:710-716` `u,p,f=∑` sums, solution, `f∈F_T`, rest | `assembled_*`(+formulas),`solution`,`solution_pin`,`force_mem`,`rest` | `simultaneous_solution`,`smooth_before_terminal_time`,`zero_initial_data` | fields | **B**; `energy_finite`/`dissipation_finite` **dropped** (implied by the two bounds). |
| `:712-717,722` per-ball agreement and blow-up | `region_agreement`, `region_blowup` (def `SpeedUnboundedAtOn`) | `singularity_each_region` | fields | **B**; ballwise `limsup` as pointwise witnesses. |
| `:718` `sup_{t<T}‖u‖₂² ≤ M²Σε_j` | `energy_bound` | `finite_energy` | `≤` (`energyEssSupT`) | **B** (`≤`, essSup spelling). |
| `:719` `∫₀^T‖∇u‖₂² dt = D²Σε_j` | `dissipation_bound` | `finite_dissipation` | `≤` | **`=`** (identity, from T15's `packetDissipationIdentity`). |
| `:698,706,720` bounded-domain / no-slip branch | (omitted, docstring note) | `no_slip_boundary`,`pressure_gauge` (Prop) | recorded as gap | **honest omission** (no bounded-domain carrier exists) — out of V1 scope. |

## `prop:conservative` — `ConservativeForcingAPI : Prop` (2 fields)

Ambient space: torus.  No parameters.

| Paper clause (`03-torus.tex`) | Lean field | A | B | ruling |
|---|---|---|---|---|
| `:723-726` `f=-∇φ`, globally defined periodic `φ` | defs `PeriodicPotentialT`,`conservativeForceT` | `domain_choice`,`globally_defined_periodic_potential`,`conservative_force` | defs | **B**; `IsPeriodicOn univ φ` excludes affine gauges. |
| `:729-731` pairing `∫_{T³} f·u = 0` | `potential_pairing` | `force_velocity_pairing_zero` (Prop) | absent | **A's clause made concrete**: Haar integral of `inner ℝ (-∇φ(t)) u(t)` `=0` on `[0,T)`. |
| `:723-728,732-737` from rest ⇒ `u≡0` on lifespan | `zero_from_rest` | `identically_zero`,`smooth_solution_from_rest`,`incompressibility`,`energy_identity`,`nonnegative_terms`,`no_breakdown` | `S.velocity=0` (FALSE) | **corrected to `∀ t∈Ico 0 T, ∀ x, u(t,x)=0`**; `ClassicalSolutionT` only constrains the `[0,T)` slab, so a global `=0` is false. **Drop** the `conservativeForceT φ∈forceClassT` premise (`MemForceT` excludes time-independent `φ`; paper imposes no such hypothesis). A's six proof-step fields dropped (they are the proof, not the statement). |
| `:724-725` bounded-domain / no-slip branch | (omitted, docstring note) | `no_slip_boundary` | recorded as gap | **honest omission** — out of V1 scope. |

## `rfl` drift checks (in `Spec.lean`, from the copied T15 vocabulary)

`example … := rfl` at `Spec.lean:431,438` verify the **registered abbreviations
vs `CompletedDenseVia`** (`CompletedDense = CompletedDenseVia q s (IsSobolevPath s)`,
`CompletedDenseHomogeneous = CompletedDenseVia q s (IsHomogeneousPath s)`).  Four
more (`:474,480,486,515,571`) pin the copied scaling defs to the registered
`Contracts.V1.scaledPacket`/`scaledPressure`/`scaledForce`/`alpha` and the
pressure-normalization formula.  All elaborate.

## Proof dependencies (copied from `RECONCILIATION.md §4 "Needs a lemma"`)

① the `eq:affine` expansion `navierStokesResidual ν (U+b) P = F + L_Ub + (b·∇)b`
(bilinearity of `spatialDerivative`); ② smooth zero-extension of the correction
across `t=1` from `tsupport b ⊆ Ioo τ₀ τ₁ ×ˢ ball`, `τ₁<1` and boundedness of
every fixed derivative of `U` there; ③ finite energy/dissipation of a compactly
supported smooth `b` + triangle inequality; ④ disjointly supported div-free curls
are linearly independent; ⑤ the `C^m` bound `≤ C_m|λ|+C_m'λ²`; ⑥ T15 support
transfer — periodized rescaled fields vanish on `fundamentalCube \ chartBall`
(from `velocity_singleCopy`/`force_singleCopy` + `eps_space`); ⑦ disjoint-support
superposition: `(U_i·∇)U_j = 0`, the finite sum solves NS, `forceClassT` and the
zero-mean gauge are closed under finite sums; ⑧ disjoint-support additivity
`‖u(t)‖₂² = Σ‖U_j(t)‖₂²` and `∫‖∇u‖² = Σ∫‖∇U_j‖²`, then `:718-719` from T15's two
identities; ⑨ torus integration by parts `∫∇φ·u = 0` and the classical energy
identity; ⑩ Haar integrability of smooth periodic lifts (shared with T20 §4).

**Implementation candidates** (from `RECONCILIATION.md §4`): T24c is close to
already proved — `formalization/NSFormalization/Paper1/ConservativeForce.lean:91`
`zero_of_negative_gradient_on_Ico` has exactly `zero_from_rest`'s hypotheses and
its corrected `∀ t∈Ico 0 T` conclusion (two `rfl` bridges needed:
`NavierStokes.ProblemStatement.UnitSpatialPeriodsOn ≡ TorusData.IsPeriodicOn`,
`Source.Insertion.residual ≡` the residual `ClassicalSolutionT.momentum` uses).
T24b's component fields come from T15's `ScalingAPI`; T24a's from `PacketAPI`
plus a bump-function library.  Shape precedents only:
`Contracts/V1/GridObservations.lean` `GridFamilyAPI` (`Fin N` family),
`Contracts/V1/ForceClasses.lean` `ForceClassesAPI.regularReference`.

## Open questions for the owner

1. **Whole-space `prop:affine`.**  `RECONCILIATION.md §0` records: the affine
   proposition is stated on whole space (the Theorem 1.1 packet, `PacketAPI`,
   terminal `1`), because `:669-671` fix `B₀⋐ℝ³` and `τ₁<1`.  Is a torus/scaled
   affine counterpart (index on `PacketImportAPI` + `ScalingAPI`, terminal `T`)
   also wanted?  That would be a **new statement**, not a re-spelling of `:668-696`.
2. **Bounded-domain / no-slip branches.**  `prop:multiple` (`:698,706,720`) and
   `prop:conservative` (`:724-725`) each have a bounded-domain / homogeneous
   no-slip branch.  No bounded-domain carrier, restriction norm, or no-slip class
   exists anywhere in the tree, so these branches are omitted with a docstring
   note.  Should a domain carrier be added (a separate work item), or does the
   torus branch suffice for the paper's Section 3?
3. **`potential_pairing` as a separate field.**  `:729-731` is a displayed
   identity (reusable torus integration-by-parts).  It is added as
   `ConservativeForcingAPI`'s first field; the owner may prefer it live in a
   shared torus-IBP contract instead (it is also implied inside `zero_from_rest`'s
   proof).
