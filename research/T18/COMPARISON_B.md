# T18 draft B — `thm:insertion` clause → Lean field table

Theorem `thm:insertion` (exact local insertion on `T³`),
`paper/sections/03-torus.tex:287-311`; proof `:312-346`.
File: `research/T18/DraftB.lean`, structure `BlowupDensity.T18.DraftB.PeriodicInsertionAPI`
(10 parameters, 43 fields), `def periodicInsertionStatement`.
Template compared against: `Contracts/V1/InsertionFamily.lean` (`InsertionFamilyAPI`, R42)
and `Contracts/V2/InsertionLifespan.lean` (`InsertionLifespanV2API`, R42.v2).

## Parameters (the objects the proof takes as given, `:287-289,312-314`)

| Lean parameter | Paper object | R42 counterpart |
|---|---|---|
| `ν : ℝ`, `P : PacketAPI ν` | viscosity; the fixed whole-space packet `(U,P,F)` that `prop:scaling` rescales | `InsertionFamilyAPI (ν) (P)` — same |
| `place : T15.Spec.PlacementData P` | `:101-107` — `T`, chart ball `B=ball(chartCenter,chartRadius)`, `x₀∈B`, `K_*`, `ε₀`, `2ε²<T`, `x₀+εK_*⊆B` | folded into `scaling.correction` (`T,x₀,B`) |
| `a : SpatialField`, `g : SpaceTimeField` | `:289` — initial velocity `v(0)=a`, reference force `g` | `InsertionFamilyAPI.a`, `scaling.correction.g` |
| `r δ : ℝ` | coordinate-ball radius `r`; regularity margin `δ` | `scaling.correction.r`, `.δ` |
| `cutoff : T16.Draft.CutoffData` | `lem:potential` cutoffs `θ,η`, potential `A`, correction family `w_ε` | inside `scaling.correction` (I02 `CorrectionAPI`) |
| `reference : ClassicalSolutionT ν a g (place.T+δ)` | `:287-288` — `(v,π,g)` regular through `T+δ` | `InsertionFamilyAPI.reference : ClassicalSolutionR …` — same shape, torus class |
| `correction : T17.Spec.CorrectionAPI ν place reference.velocity r δ cutoff` | `lem:correction` — `H_ε`, `eq:wE`/`eq:Hmixed`/`eq:HHs` bounds; carries `LocalPotentialAPI` (`w_ε`) + `LocalizationAPI` | `scaling : ScalingAPI ν P` (bundles I02/I01) |

Choice: parameters vs fields. R42 bundles everything into one `scaling` field and
takes only `(ν,P)`.  The torus scaling/correction chain is **not** one registered
contract (the T14/T15 `PacketImportAPI`/`ScalingAPI` live only in
`research/T15/Spec.lean`, outside this brief's copy allowance), so the ambient data
is taken as **parameters** (packet, placement, reference, cutoff, correction) — the
brief's suggested split.  This keeps `periodicInsertionStatement` a clean
`∀ (data), (hyps) → Nonempty (PeriodicInsertionAPI …)` with no dependent-field
`HEq` pinning.

## Hypotheses (paper givens not forced by parameter types)

| Field | Paper | R42 counterpart |
|---|---|---|
| `delta_pos` | `:288` `δ>0` | reference horizon `T+δ` |
| `reference_force_mem` (`g∈𝓕`) | `:289` | `InsertionLifespanAPI` hyp `memForce` |
| `initial_mem` (`a∈𝓧`) | `:289` | `a` typed by `ClassicalSolutionR` |
| `ε₀, eps_pos, eps_le_cutoff` | `:290` "sufficiently small `ε>0`" | `ε₀, eps_pos, eps_le_scaling` |

## The inserted triple and `eq:insertion` (`:314`)

| Field | Clause | R42 counterpart |
|---|---|---|
| `velocity, pressure, force` | `ε ↦ (u_ε,p_ε,g_ε)` | `velocity, pressure, force` |
| `velocity_formula` | `u_ε=v+w_ε+U_ε`; `U_ε=periodicScaledPacket` | `velocity_formula` (whole-space `scaling.U`) |
| `pressure_formula` | `p_ε=π+P_ε` normalized by `∫_{T³}p=0` (`:318-320`) | **TORUS** — `pressure_formula` uses compact gauge `π+P_ε` (`InsertionFamily.lean:183`); torus imposes `normalizePressureT` |
| `force_formula` | `g_ε=g+H_ε+F_ε`; `H_ε=correctionForce`, `F_ε=periodicScaledForce` | `force_formula` |

## Solution / lifespan / blow-up (clause (i), `:291-292,338-345`)

| Field | Clause | R42 counterpart |
|---|---|---|
| `force_mem` (`g_ε∈𝓕`) | `:289,339` | (R42 `forceDifference_compact` on the diff) |
| `forceDifference_mem` | `:339-341` `g_ε-g∈𝓕` | `forceDifference_compact` |
| `velocity_smooth, pressure_smooth, initial, incompressible, momentum, history, velocity_periodic` | `:329-337`, (ii) `:294` | `velocity_smooth,pressure_smooth,initial,incompressible,momentum,history` (+`velocity_periodic` torus-only) |
| `solution` | `:338,344-345` full-horizon `ClassicalSolutionT` | `InsertionLifespanV2API.solution` |
| `maximal` | `:342-344` **TORUS** `IsMaximalPeriodicSolution` (not R³ `IsMaximalSolution`) | `InsertionLifespanV2API.maximal` |
| `lifespan` (`T_max=T`) | (i) `:291,344-345` | `InsertionLifespanAPI.lifespan` |
| `blowup` (`SpeedUnboundedAt`) | (i) `:291-292` | `InsertionFamilyAPI.blowup` |
| `blowup_limsup` (`limsupLeft…=⊤`) | (i) `:291-292` | `InsertionLifespanV2API.blowup_limsup` |

## Two vanishing cross-transport terms (`:322-328`, proof of `eq:insertion`)

| Field | Clause | R42 counterpart |
|---|---|---|
| `crossTransport_background_advects_packet` | `(b_ε·∇)U_ε=0`, `b_ε=v+w_ε` | **TORUS-EMPHASIZED** — R42 folds this into `momentum` prose ("cross-advection terms … vanish", `04-whole-space.tex:51`); stated here as an explicit identity |
| `crossTransport_packet_advects_background` | `(U_ε·∇)b_ε=0` | same |

Both written with the registered `spatialDerivative` (directional Fréchet
derivative), the copied `periodicScaledPacket` (`U_ε`) and `correctedBackground`
(`b_ε`).  "Both terms are identically zero" (`:325`) ⇒ two separate `= 0` fields.

## Localization (clause (iii), `:293-295`)

| Field | Clause | R42 counterpart |
|---|---|---|
| `velocityDifference_divFree` | `:295` `u_ε-v` divergence free | `velocityDifference_divFree` |
| `diffSupportRadius(_pos)` | `:293-295` fixed radius `ρ` for `O(ε)` diameter | — (R42 uses `scaling.correction.r`) |
| `velocityDifference_support` | `:295` support ⊆ **TORUS** `periodicSet (ball x₀ (ε·ρ))` | `velocityDifference_support` (whole-space `ball x₀ r`) |
| `diffSupport_in_chart` | `:293-295` "inside the chosen ball" | (implicit in R42's ball choice) |

## Three closeness rates (clause (iv), `:296-306`) + `s<0` tail (`:309-310`)

| Field | Clause | R42 counterpart |
|---|---|---|
| `energyRate` | `eq:Eclose` `:300-302` `‖u_ε-v‖_{E_T}≤(M+D)ε^{1/2}+Cε^{3/2}`; `M=P.energyBound`,`D=P.dissipationBound`,`C=correction.energyConst`; torus `energyENormT` | `energyRate` (whole-space `energyENorm`) |
| `forceDiffMixedConst(_nonneg)`, `forceDifference_spatial_memLp`, `forceDifference_mixed_bound` | `eq:Fclose` `:303-304` `‖g_ε-g‖_{L^q_tL^p_x}≤C_{p,q}(ε^{α}+ε^{α+1})`, `α=-3+3/p+2/q`; copied `mixedLebesgueENormT` | **TORUS** — R42 states only `forceConvergence` (Tendsto), no explicit rate |
| `forceDiffSobolevConst(_pos)`, `forceDifference_sobolev_memLp`, `forceDifference_sobolev_bound` | `eq:Hsclose` `:305-306` `‖g_ε-g‖_{L¹_tH^s_x}≤C_s(ε^{1/2-s}+ε^{3/2-s})`, **`0≤s<1/2`**; registered `forceSobolevENormT 1 s` | **TORUS** — explicit rate; R42 has only `forceConvergence` |
| `forceDifference_negativeSobolev_tendsto` | `:309-310` `s<0`: force diff → 0 in `L¹_tH^s_x` | `forceConvergence` (Tendsto form) |

Honesty guards (`forceDifference_spatial_memLp`, `forceDifference_sobolev_memLp`)
mirror `CorrectionAPI.force_spatial_memLp`/`forceSobolev_memLp`: no norm bound is
stated without an integrability/representability hypothesis on that norm (no
junk-value trap).  `ν>0` is carried by `correction.viscosity_pos`; `ε∈Ioc 0 ε₀`
guards every quantitative field.

## Ambiguities / decisions recorded

1. **Pressure gauge.** `eq:insertion` writes `p_ε=π+P_ε`, but `:318-320` says
   "subtract its spatial mean to normalize `p_ε`".  I render `pressure_formula`
   with `normalizePressureT` (the `∫_{T³}p=0` gauge), the torus-faithful reading;
   R42's whole-space twin keeps the un-normalized compact gauge.  A second reader
   might state `p_ε-π=P_ε` (compact) plus a separate gauge field.
2. **Blow-up form.** Stated in **both** the pointwise (`blowup`/`SpeedUnboundedAt`)
   and essential-sup (`blowup_limsup`/`limsupLeft`,`speedENorm`) forms, matching
   R42.v2.  `speedENorm` is the `L^∞(R³)` ess-sup, which for a periodic field is
   the `L^∞(T³)` norm.
3. **`U_ε,P_ε,F_ε` periodization.** `velocity_formula` uses the copied
   `periodicScaledPacket`; `P_ε,F_ε` use the two new lattice-sum helpers
   `periodicScaledPressure`/`periodicScaledForce` (built from the registered
   whole-space `scaledPressure`/`scaledForce`), the only defs this file adds.
4. **`s<1/2` vs `s≤1`.** `eq:Hsclose` range is `0≤s<1/2` (strict), narrower than
   `lem:correction`'s `eq:HHs` `0≤s≤1`; kept faithful to the theorem statement.
5. **Support radius.** clause (iii) says "diameter `O(ε)`"; modelled by a carried
   positive `diffSupportRadius` with `ε·ρ` scaling and a `⊆B` inclusion, rather
   than reusing `r` (which bounds `w_ε` only, not `U_ε`).

## "Needs a lemma" — fields the proof will consume

- **T11** `PeriodicLocalTheoryAPI` (`Contracts/V1/TorusLocalTheory.lean`):
  `velocity_unique`/`pressure_unique` and `exists_maximal`/`maximal_unique` for
  `maximal` and the `≥T` half of `lifespan` (`:342-344`, "uniqueness in
  `prop:local` identifies the constructed velocity with the maximal solution").
- **T11** `PeriodicContinuationH3API.{extendsBeyond, lifespanInfiniteOfLocallyFinite}`
  for the `≤T` half of `lifespan` (`:344-345`): an extension past `T` would have a
  finite squared-`H²` integral, contradicting `blowup`.
- **T12** `MeanZeroSobolevCalculusAPI.boundedRepresentative`
  (`research/T12/Spec.lean:383`, `H²(T³)↪L^∞(T³)`) for the `≤T` half: an extension
  bounded in `C_tH²` near `T` is bounded in `L^∞`, contradicting `blowup_limsup`.
- **T16** `LocalPotentialAPI.correction_cancels`/`potential_curl` (carried inside
  `correction.potential`) for `crossTransport_*` (`eq:bgzero` ⇒ `b_ε=0` on a
  neighbourhood of `supp U_ε`).
- **T17** `CorrectionAPI.correction_energy_bound` (`eq:wE`) for the `Cε^{3/2}`
  term of `energyRate`; `force_mixed_bound` (`eq:Hmixed`) and `force_sobolev_bound`
  (`eq:HHs`) for the `ε^{α+1}`/`ε^{3/2-s}` terms of `forceDifference_mixed_bound`
  and `forceDifference_sobolev_bound`; `force_smooth`/`force_support`/`force_periodic`
  for `force_mem`/`forceDifference_mem`.
- **T15/prop:scaling** (`research/T15/Spec.lean`, outside this copy set):
  `‖U_ε‖_{L^∞L²}=ε^{1/2}M`, `‖∇U_ε‖_{L²L²}=ε^{1/2}D` (`eq:packetEscale`) for the
  `(M+D)ε^{1/2}` term of `energyRate`; `‖F_ε‖_{L^qL^p}=ε^{α}‖F‖` (`eq:packetFscale`)
  and `‖F_ε‖_{L¹H^s}≤C_s(ε^{1/2}+ε^{1/2-s})` (`eq:packetHs`) for the `ε^{α}`/`ε^{1/2-s}`
  terms.  **Registration gap**: these torus scaling APIs are not yet a registered
  contract; T18's assembly will need one (or T15/T24's `ScalingAPI` promoted).
- **T13** `LocalizationAPI` (carried inside `correction.localization`) transfers the
  Euclidean `Ḣ^s` bounds to `H^s(T³)` for `eq:Hsclose`.

## Implementation candidates (`formalization/NSFormalization/Paper1/`)

- `PeriodicInsertion.lean`: `def velocity/pressure/force`, `def before`,
  `structure Properties (ν r T τ …)`, `theorem of_insertion` — the assembled
  inserted triple and its property record (closest existing analogue of
  `PeriodicInsertionAPI`).
- `PeriodicCrossComponentTransport.lean` / `…Bilinear.lean` /
  `PeriodicProjectedTransport.lean`: `transportCoeff`, `transportVector`,
  `projectedTransport`, `projectedTransport_divergence_free` — the cross-transport
  cancellation machinery for `crossTransport_*`.
- `PeriodicInsertionSupport.lean`: `eventually_supportedInCube_insertionForce` etc.
  — support/localization for `velocityDifference_support`/`forceDifference_ball`.
- `PeriodicInsertionFiniteEndpoints.lean`, `…EndpointRateBound.lean`,
  `…PositiveConvergence.lean`, `…WholeEndpointRates.lean`: the `L¹H^s` endpoint
  rate and `→0` convergence for `forceDifference_sobolev_bound` and
  `forceDifference_negativeSobolev_tendsto`.
- `InsertionEnergy.lean`: energy-norm assembly for `energyRate`.
