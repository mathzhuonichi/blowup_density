# T23 draft B — `cor:boundary` (interior no-slip insertion): clause → field table

Source: `paper/sections/03-torus.tex:632-666` (corollary `:632-651`, proof
`:652-666`) plus the norm preamble `:600-631` (`eq:restriction-norm` `:603-605`,
`eq:zero-extension` `:610-614`). File: `research/T23/DraftB.lean`, namespace
`BlowupDensity.T23.DraftB`. All fields live in `structure BoundaryInsertionAPI`
unless a `def`/`ClassicalSolutionOmega`/`T22.Draft` prefix is given.

`cor:boundary` = `thm:insertion` (T18 `PeriodicInsertionAPI`) restricted to a
bounded domain `Ω`. The table gives the T18 counterpart field (or "torus-only" /
"domain-only") next to each domain field.

## A. Statement clauses (`:632-651`)

| Paper clause (line) | Lean field | T18 counterpart | Notes |
|---|---|---|---|
| `Ω` bounded box or bounded smooth domain (`:632-633`) | `domain : BoundedDomain Ω` | none (torus is all of `R³`) | `BoundedDomain` = open ∧ bounded ∧ nonempty ∧ measurable; box-vs-smooth distinction not encoded (ambiguity §C) |
| for some `δ>0` (`:634`) | `delta_pos` | `PeriodicInsertionAPI.delta_pos` | identical |
| `(v,π,g)` smooth no-slip solution on `[0,T+δ]` (`:634`,`:648`) | parameter `reference : ClassicalSolutionOmega ν Ω a g (place.T+δ)` | param `reference : ClassicalSolutionT …` | new domain solution record §1 |
| `g` smooth on `Ω̄×[0,∞)`, temporal support compact in `(0,∞)` (`:635`) | `reference_force_mem : g ∈ forceClassOmega Ω` | `reference_force_mem : g ∈ forceClassT` | torus `MemForceT` → `MemForceOmega` (no periodicity, slab smoothness) |
| smoothness = restriction of `C∞` from open nbhd of the slab (`:636-639`) | `def SmoothOnClosedSlab` (used in `ClassicalSolutionOmega`, `MemForceOmega`) | torus uses `ContDiffOn … univ` | literal neighborhood encoding of the paper convention |
| equation & incompressibility in `Ω` (`:641`) | `ClassicalSolutionOmega.momentum`, `.divergence` (`∀ x ∈ Ω`) | `ClassicalSolutionT.momentum`,`.divergence` (all `x`) | restricted to `Ω` |
| `v|_∂Ω = 0` (`:641`) | `ClassicalSolutionOmega.no_slip` | torus-only: none | new |
| pressure normalized by zero spatial mean (`:644`) | `ClassicalSolutionOmega.pressure_gauge` (`∫_Ω p=0`); `def domainNormalizePressure` | `ClassicalSolutionT.pressure_gauge` (`∫_{T³}p=0`) | mean over `Ω` |
| initial velocity `a` (smooth div-free no-slip) (`:641`,`:646`) | `initial_mem : a ∈ initialClassOmega Ω` | `initial_mem : a ∈ initialClassT` | `initialClassOmega`: smooth on `cl Ω`, div-free in `Ω`, no-slip |
| existence of the compatible reference is assumed (`:648`) | reference is a **parameter**, not a conclusion | same (T18 threads `reference`) | — |
| construction applies inside any prescribed interior ball (`:646`) | `interiorBall_in_domain : closure (ball …) ⊆ Ω`; velocity via `scaledPacket` (un-periodized) | `PlacementData.chartBall_in_cube` (torus cube) | domain adds the ⊆ Ω placement; §C on the inherited cube field |
| preserving the initial velocity (`:646`) | `initial : u_ε(0,·)=a on Ω` | `PeriodicInsertionAPI.initial` | `∀ x ∈ Ω` |
| preserving no-slip boundary values (`:646`) | `noSlip_preserved`; mechanism `collar_agreement` | torus-only: none | new |
| energy estimates use `L²(Ω)` (`:647`) | `energyRate` via `def domainEnergyENorm` | `energyRate` via `energyENormT` (Haar) | `L²(Ω) = eLpNorm … (volume.restrict Ω)` = T22 order-0 restriction norm |
| force estimates use `L¹(0,∞;H^s(Ω))`, restriction norm (`:647-649`) | `forceDifference_sobolev_bound` via `def domainForceSobolevENorm` | `forceDifference_sobolev_bound` via `forceSobolevENormT` | `∫⁻_{(0,∞)} domainSobolevENorm Ω s (restrictField Ω …)` |
| for every real `s`, domain & zero-extended norms comparable, const. indep. of `ε` (`:649-650`) | `domain_zeroExt_comparison` (`∀ s, ∃ C>0, ∀ ε`) | torus-only: none | consumes `norms.zeroExtensionComparison` (§D) |
| convergence assertion remains `s<1/2` (`:650`) | `forceDifference_convergence` (`0≤s<1/2`), plus `forceDiffSobolevConst_pos` range `<1/2` | T18 bound range `s<1/2` for `eq:Hsclose` | range stops at `1/2` (not `1` as `eq:HHs`) |

## B. Proof clauses (`:652-666`) — what the conclusion adds / how

| Proof clause (line) | Lean field | T18 counterpart | Notes |
|---|---|---|---|
| vector potential / cutoff estimates local; supports in a smaller closed ball ⋐ Ω (`:653-654`) | `interiorBall_in_domain`; `velocityDifference_support` (single ball); `diffSupport_in_chart` | `velocityDifference_support` uses `periodicSet (ball …)` | TORUS: single whole-space ball, no `periodicSet` |
| momentum computation unchanged (`:655`) | `momentum`; `crossTransport_background_advects_packet`; `crossTransport_packet_advects_background` | same three (periodized packet) | un-periodized `scaledPacket` |
| new velocity = reference in a fixed boundary collar for all times before blowup (`:655`) | `collar_agreement` | torus-only | fixed collar = complement of fixed `B` |
| ⇒ no-slip boundary values preserved (`:655`) | `noSlip_preserved` | torus-only | consequence of collar + `reference.no_slip` |
| force correction supported in same interior region, same smooth time extension (`:655-656`) | `force_mem`,`forceDifference_mem` (∈ `forceClassOmega`); `forceDifference_spatialSupport` | `force_mem`,`forceDifference_mem` (∈ `forceClassT`) | `forceClassT`→`forceClassOmega` |
| `0≤s<1/2`: Euclidean scaling bounds zero-extensions in `L¹(0,∞;H^s(R³))` (`:658-660`) | `def zeroExtForceSobolevENorm`; `domain_zeroExt_comparison` (lower side) | — | the whole-space norm the scaling proof bounds |
| `s<0`: `‖E_0(g_ε-g)‖_{H^s(R³)} ≤ ‖·‖_{L²(R³)}` at each time (`:659-660`) | `forceDifference_negativeSobolev_tendsto` | T18 `forceDifference_negativeSobolev_tendsto` (torus) | domain restriction norm → 0 |
| all supports (incl. after `T`) in one fixed compact interior ball `K`, all small `ε` (`:661-662`) | `forceDifference_spatialSupport` (`∀ t` incl. `t≥T`, `x ∈ cl B`) | torus-only | the `ε`-independence source |
| `eq:zero-extension` ⇒ domain estimates + scale-independent comparison after time integration (`:662-663`) | `domain_zeroExt_comparison`; `forceDifference_sobolev_bound` | — | consumes `norms.zeroExtensionComparison` + `forceDifference_spatialSupport` |
| energy estimates follow by integrating over that ball (`:664`) | `energyRate` | `energyRate` | `E_T(Ω)` |
| classical no-slip uniqueness from the same difference-energy calc as `prop:local`; boundary terms vanish (`:664-665`) | `noSlip_uniqueness` | `PeriodicLocalTheoryAPI.velocity_unique` (torus) | domain uniqueness; boundary terms vanish |
| the constructed solution is singular exactly at `T` (`:666`) | `solution`; `lifespan`; `blowup`; `blowup_limsup`; `def domainMaximalLifespan` | `solution`,`lifespan`,`blowup`,`blowup_limsup`,`maximal` | domain lifespan via `ClassicalSolutionOmega` |

Threshold bookkeeping (`ε₀`,`eps_pos`,`eps_le_scaling`,`eps_le_cutoff`) and the
three `eq:insertion` formulas (`velocity_formula`/`pressure_formula`/`force_formula`)
mirror T18 with the un-periodized packet and the `∫_Ω` gauge.

## C. Choices, and ambiguities to reconcile

1. **Un-periodized packet (torus differs #1).** The domain uses the registered
   whole-space `scaledPacket`/`scaledPressure`/`scaledForce` (imported), *not*
   `periodizedScaledVelocity` etc. Rationale: an arbitrary bounded `Ω` may
   contain several lattice translates, so a periodized packet would be wrong;
   the corollary is explicitly single-copy inside one interior ball. Consequence:
   the torus `ScalingAPI` (periodization layer) is **not threaded**; `prop:scaling`
   enters through `P.energyBound`/`P.dissipationBound` and the constant fields
   `energyConst`, `forceDiffSobolevConst` (exactly as T18's own bound fields carry
   their constants — T18's `energyRate` uses `correction.energyConst`, not
   `scaling`). **Reconcile:** if draft A threads a scaling record, decide whether
   the domain needs it in the statement or only in the proof.
2. **`ScalingAPI`/`CorrectionAPI` not threaded.** T18 threads
   `scaling : ScalingAPI` and `correction : CorrectionAPI`. Both are torus
   records (periodization; one-copy torus support via `torusSpatialSupport`).
   Draft B threads only `D : CutoffData` (needed for `w_ε = D.correction ε` and
   `correctionForce`) and inlines the correction/scaling constants as fields.
   **Reconcile:** whether to thread the correction record for maximal mirror, or
   inline (draft B's choice, to avoid dragging torus support fields into a domain
   statement).
3. **`PlacementData.chartBall_in_cube` (`⊆ interior fundamentalCube`).** Reused
   verbatim from T15.Draft; it is a torus artifact (single-copy on the unit
   cube). Draft B adds `interiorBall_in_domain` (`⊆ Ω`) for the actual domain
   condition. Reusing `thm:insertion`'s construction chart makes both consistent
   (choose a small interior ball in the cube∩Ω overlap), but a clean bounded-domain
   V2 should drop `chartBall_in_cube`. **Reconcile:** whether draft A reuses
   `PlacementData` or defines a cube-free placement.
4. **`BoundedDomain` (box vs smooth boundary).** Encoded as open ∧ bounded ∧
   nonempty ∧ measurable. The box-vs-smooth distinction governs only elliptic
   regularity for the *assumed* reference (`:648`), which the corollary takes as
   a hypothesis, so it is not separately encoded. **Reconcile / needs a
   definition:** a faithful `IsBox ∨ HasSmoothBoundary` predicate (Mathlib
   `IsOpen` + a `C^k` boundary chart notion) if draft A encodes it.
5. **Slab smoothness convention.** `SmoothOnClosedSlab` encodes the paper's
   "restriction of `C∞` from an open neighborhood" literally (∃ open `N ⊇ I×cl Ω`,
   `ContDiffOn ∞ f N`), rather than the local impl's `ContDiffOn ∞ f (Icc … ×ˢ
   closure Ω)` (`BoundaryCorollary.lean:32`). **Reconcile:** which convention.
6. **Pressure gauge as `∫_Ω = 0`.** The paper says pressure "may be normalized"
   (`:644`); draft B imposes it (zero `Ω`-integral) in `ClassicalSolutionOmega`
   and `domainNormalizePressure` subtracts the `Ω`-average. **Reconcile:** whether
   the gauge is mandatory or optional.
7. **No drift-`rfl` checks needed.** None of the copied blocks (T13.Spec
   `fundamentalCube`, T15.Draft `PlacementData`, T16.Draft `CutoffData`/
   `correctedBackground`, T17.Spec `correctionForce`, all of T22.Draft) overlaps a
   *registered* name, so no `example … := rfl` drift check is required. The
   would-be overlap (`scaledVelocity = Contracts.V1.scaledPacket`, `:344`) is
   avoided by using the registered `scaledPacket` directly.

## D. "Needs a lemma": which upstream fields the proof will consume

| Domain field to prove | Consumes |
|---|---|
| `momentum`, cross-transport | T18 `PeriodicInsertionAPI.momentum` / cross-transport (un-periodized), `lem:correction` (`correctionForce`), `lem:potential` (`D`) |
| `energyRate` | `lem:packetenergy` (`P.energyBound`,`P.dissipationBound`), `eq:wE`; `BoundaryCorollary.bounded_energy_restriction` route (`domainL2Sq_le_whole`,`domainDissipation_le_whole`, `LocalizationBoundary.lean:64,91`) |
| `forceDifference_sobolev_bound` | `prop:scaling` `eq:packetHs`; `eq:zero-extension` upper side (`norms.zeroExtensionComparison`) |
| `domain_zeroExt_comparison` | **`norms.zeroExtensionComparison`** (T22 `BoundedDomainNormAPI`, `eq:zero-extension`) + `forceDifference_spatialSupport` (fixed `K`) |
| `forceDifference_negativeSobolev_tendsto` | `eq:zero-extension` `s<0` case + `orderZero`/`L²` monotonicity (`norms.orderZero`) |
| `noSlip_preserved` | `collar_agreement` + `reference.no_slip` + `interiorBall_in_domain` (frontier disjoint from interior ball) |
| `noSlip_uniqueness` | `prop:local` difference-energy identity with vanishing boundary terms (`C01.EnergyIdentity` analog on `Ω`) |
| `lifespan`,`solution`,`maximal` | T11 (`prop:local`) uniqueness/continuation on `Ω`; `H²↪L∞` (Mathlib) |

## E. Implementation candidates (cite only; never imported — `BoundaryCorollary.lean:90` has a `sorry`)

`formalization/NSFormalization/Paper1/` (grep `^(def|structure|theorem)`):

* `BoundaryCorollary.lean`: `BoundedReference:28`, `BoundedFlow:42`,
  `domainSobolevNorm:20`, `domainForceNorm:24`, `noSlip_of_boundary_agreement:54`,
  `bounded_energy_restriction:64`, `exists_interior_noSlip_insertion:76` (**`sorry` at `:90`**).
* `BoundaryCorollaryCorrected.lean`: `disjoint_frontier_of_subset_interior:19`
  (the collar⇒no-slip geometry), `InteriorNoSlipInsertionContract:28`,
  `corrected_interior_noSlip_insertion:45`.
* `BoundaryReferenceRestriction.lean`: `boundedFlow_of_reference:12`,
  `noSlip_of_supported_difference:40`, `tsupport_difference_subset:58`,
  `noSlip_of_reference_and_supported_difference:76`, `reference_noSlip_on_horizon:108`,
  `noSlip_of_horizon_support:126`.
* `BoundarySupportComposition.lean`: `noSlip_of_composed_supported_differences:13`.
* `BoundaryAnalyticBridge.lean`: `BoundedFlowData:22`, `boundedFlow_of_data:37`,
  `ExplicitInsertionFlowBinding:48`, `reference_supported_noSlip_on_horizon:57`.
* `LocalizationBoundary.lean`: `domainL2Sq:60`/`_le_whole:64`,
  `domainDissipation:87`/`_le_whole:91` (the `L²(Ω) ≤ L²(R³)` energy route);
  `fractionalKernel*` and `periodicSobolevNorm_periodize_interpolation_complex:189`
  (the `eq:zero-extension`/localization analytic core).
