# T23 `cor:boundary` (interior no-slip insertion) — merged clause → field table

Reconciled specification: `research/T23/Spec.lean`, namespace
`BlowupDensity.T23.Spec` (`structure BoundaryInsertionAPI` +
`def boundaryInsertionStatement`). Source: `paper/sections/03-torus.tex:632-666`
(corollary `:632-651`, proof `:652-666`), norm preamble `:600-631`
(`eq:restriction-norm` `:603-605`, `eq:zero-extension` `:610-614`).

Base draft **B** (lane 374, Opus); three binding imports from draft **A**
(lane 368, codex gpt-5.6-sol): the domain-shape disjunction, the record-form
`maximal` field, and — jointly with B — the cube-free interior placement. Rulings
are `research/T23/RECONCILIATION.md` §2 (verbatim reasons condensed here). All
reconciled fields live in `structure BoundaryInsertionAPI` unless a
`def`/`DomainPlacementData`/`ClassicalSolutionOmega`/`T22.Draft` prefix is given.

Field counts: `DomainPlacementData` 16, `ClassicalSolutionOmega` 10,
`BoundaryInsertionAPI` 48 (= B's 47 + the added `maximal`), plus 31 top-level
`def`/`structure` and `boundaryInsertionStatement`.

## A. Statement clauses (`:632-651`)

| Paper clause (line) | Reconciled Lean field | Draft A | Draft B | T18 counterpart | Ruling (RECONCILIATION §2) |
|---|---|---|---|---|---|
| `Ω` bounded box or bounded smooth domain (`:632-633`) | `domain : IsBoundedBoxOrSmoothDomain Ω` (`IsBoxDomain ∨ IsRegularLevelDomain`, + `Ω.Nonempty`) | `IsBoundedBoxOrSmoothDomain`, `domain_shape` | `domain : BoundedDomain` (open∧bdd∧nonempty∧meas) | none (torus is all of `R³`) | **A's disjunction + B's nonemptiness.** Paper states box-or-smooth; fidelity keeps the disjunction; add `Nonempty` (smooth branch may be empty). |
| `ν>0`, target `T>0` (`:632-634`) | statement `0 < ν`; `place.time_pos` | `viscosity_pos`, `time_pos` | `place.time_pos` | `PeriodicInsertionAPI` viscosity + `place.time_pos` | both |
| margin `δ>0` (`:634`) | `delta_pos` | `delta_pos` | `delta_pos` | `PeriodicInsertionAPI.delta_pos` | both identical |
| `(v,π,g)` smooth no-slip reference on `[0,T+δ]`, assumed (`:634`,`:645`,`:648`) | param `reference : ClassicalSolutionOmega ν Ω a g (place.T+δ)` (10-field record) | free `v,π` params + `IsBoundedClassicalSolution` predicate | `reference : ClassicalSolutionOmega …` | param `reference : ClassicalSolutionT …` | **B.** structured record mirroring `ClassicalSolutionT` (`univ→cl Ω`, no-slip added, eqn on `Ω`); T18 §2 already ruled record over free `v,π`+pins. |
| smoothness = restriction of `C∞` from open nbhd of the slab (`:636-639`) | `def SmoothOnClosedSlab` (∃ open `N⊇I×ˢ cl Ω`, `ContDiffOn ∞ f N`) | `SmoothOnClosedDomainSlab` | `SmoothOnClosedSlab` | torus `ContDiffOn … univ` | both literal/honest (agree). |
| `g` smooth on `Ω̄×[0,∞)`, temporal supp compact in `(0,∞)` (`:635-637`) | `reference_force_mem : g ∈ forceClassOmega Ω` (`MemForceOmega`) | `DomainForceClass`, `reference_force_mem` | `forceClassOmega Ω` | `reference_force_mem : g ∈ forceClassT` | both (agree); periodicity dropped, slab smoothness. |
| equation & incompressibility in `Ω` (`:641`) | `ClassicalSolutionOmega.momentum`,`.divergence` (`∀ x∈Ω`) | `reference_momentum`,`reference_divergence` | `.momentum`,`.divergence` | `ClassicalSolutionT.momentum`,`.divergence` (all `x`) | both (agree, restricted to `Ω`). |
| `v|_∂Ω=0` (`:641`) | `ClassicalSolutionOmega.no_slip` | `reference_no_slip` | `.no_slip` | torus-only: none | both (agree, new for domain). |
| pressure may be normalized by zero spatial mean (`:644`) | `ClassicalSolutionOmega.pressure_gauge` (`∫_Ω p=0`); `def domainNormalizePressure` | `domainMean`, `reference_pressure_gauge` | `pressure_gauge`; `domainNormalizePressure` | `ClassicalSolutionT.pressure_gauge` | **B (gauge imposed by construction).** `domainNormalizePressure` subtracts the `Ω`-mean; A's two pressure fields over-constrain (`∫_Ω P_ε=0`). Owner Q5. |
| initial velocity `a` smooth div-free no-slip (`:641`,`:646`) | `initial_mem : a ∈ initialClassOmega Ω` | `initial_datum` | `initialClassOmega Ω` | `initial_mem : a ∈ initialClassT` | both (agree). |
| construction applies inside any prescribed interior ball (`:646`) | **cube-free** `place : DomainPlacementData` + `interiorBall_in_domain : closure(ball chartCenter chartRadius) ⊆ Ω`; support at `place.x₀` | ball **centred at origin** `ball (0) (ε·ρ)`, `difference_support_interior` | `interiorBall_in_domain` + torus `PlacementData.chartBall_in_cube` | `PlacementData.chartBall_in_cube` (torus cube) | **Neither as-is — B's mechanism, cube dropped.** A is FALSE (forces `0∈interior Ω`); B is vacuous off `(0,1)³`. Fix: cube-free `DomainPlacementData` centred at free `x₀`. §"False clauses" #1–2. |
| preserving the initial velocity (`:646`) | `initial : u_ε(0,·)=a on Ω` | `initial` | `initial` | `PeriodicInsertionAPI.initial` | both (agree). |
| preserving no-slip boundary values (`:646`) | `noSlip_preserved`; mechanism `collar_agreement` | `no_slip`, `boundary_collar_preserved` | `noSlip_preserved`,`collar_agreement` | torus-only: none | **B's collar** = complement of the fixed ball (`ε`-independent); A's extra abstract collar set is redundant. |
| energy uses `L²(Ω)` (`:647`) | `energyRate` via `def domainEnergyENorm` (`essSup+lintegral`) | `domainEnergyENorm` + `DomainEnergySlicesMemLp`/`energy_slices_memLp` | `domainEnergyENorm` (no guard) | `energyRate` via `energyENormT` | **B (no energy guard).** `essSup+lintegral` has no representative-`⨅`, so `≤finite` is self-guarding; drop A's `MemLp` guards. |
| force uses `L¹(0,∞;H^s(Ω))`, restriction norm (`:647-649`) | `forceDifference_sobolev_bound` via `def domainForceSobolevENorm := ∫⁻ domainSobolevENorm (restrictField …)` | joint-path `⨅` over `RealVectorSobolev`-paths + `MemDomainForceSobolev` | per-slice `∫⁻ domainSobolevENorm` | via `forceSobolevENormT` | **B (per-slice).** `eq:restriction-norm` is the per-slice quotient norm; `L¹_t` of it consumes T22's `domainSobolevENorm` directly. A's joint `⨅` is a different (larger) object. |
| domain & zero-extended norms comparable, `C` indep. of `ε`, all real `s` (`:649-650`) | `domain_zeroExt_comparison` (`∀s, ∃C>0, ∀ε`), threads `norms : BoundedDomainNormAPI`, consumes `norms.zeroExtensionComparison` | `zeroExtension_comparison` (raw, not threaded) | `domain_zeroExt_comparison` (threaded) | torus-only: none | **B.** `BoundedDomainNormAPI` unregistered (T22) ⇒ must be threaded (the T15↔T18 pattern); A's raw field is not provable from A's params. |
| convergence assertion remains `s<1/2` (`:650`) | `forceDifference_convergence` (`0≤s<1/2`), `forceDiffSobolevConst_pos` range `<1/2` | `forceDifference_sobolev_tendsto` | `forceDifference_convergence` | T18 range `s<1/2` for `eq:Hsclose` | both (agree); range stops at `1/2`. |

## B. Proof clauses (`:652-666`)

| Proof clause (line) | Reconciled Lean field | Draft A | Draft B | T18 counterpart | Ruling |
|---|---|---|---|---|---|
| supports in a smaller closed ball ⋐ Ω (`:653-654`) | `velocityDifference_support` (single ball at `place.x₀`), `diffSupport_in_chart`, `interiorBall_in_domain` | origin-centred support | single ball at `place.x₀` | `velocityDifference_support` uses `periodicSet (ball …)` | **B.** single whole-space ball (un-periodized); the T18 single-ball trap does not apply (field not periodic). |
| momentum computation unchanged (`:655`) | `momentum`; `crossTransport_background_advects_packet`; `crossTransport_packet_advects_background` (un-periodized `scaledPacket`) | same three (abstract fields) | same three | same three (periodized packet) | **B.** un-periodized `scaledPacket`. |
| new velocity = reference in a fixed boundary collar (`:655`) ⇒ no-slip preserved | `collar_agreement` ⇒ `noSlip_preserved` | abstract `collar` set + `boundary_collar_preserved` | `collar_agreement` (collar = `Bᶜ`) | torus-only | **B.** collar = complement of fixed chart ball, `ε`-independent. |
| force correction in same interior region, same smooth time extension (`:655-656`) | `force_mem`, `forceDifference_mem` (∈ `forceClassOmega`); `forceDifference_spatialSupport` | `force_mem`, `forceDifference_mem` | same + `forceDifference_spatialSupport` | `force_mem`,`forceDifference_mem` (∈`forceClassT`) | both. |
| all supports incl. after `T` in one fixed compact interior ball `K` (`:661-662`) | `forceDifference_spatialSupport : ∀ε,∀t,∀x, g_ε−g≠0 → x∈cl B` | per-`ε` class membership only | `forceDifference_spatialSupport` (all `t`) | torus-only | **B.** the `ε`-independent fixed `K` (incl. post-`T`) makes `eq:zero-extension` scale-independent. |
| `s<0`: `‖E_0(g_ε−g)‖_{H^s} ≤ ‖·‖_{L²}` at each time (`:659-660`) | `forceDifference_negativeSobolev_tendsto` | `forceDifference_negativeSobolev_memLp`,`_tendsto` | `forceDifference_negativeSobolev_tendsto` | T18 torus analogue | both (agree). |
| energy estimates by integrating over the ball (`:664`) | `energyRate` (`domainEnergyENorm`) | `energyRate` | `energyRate` | `energyRate` | both. |
| classical no-slip uniqueness, same diff-energy calc as `prop:local`; boundary terms vanish (`:664-665`) | `noSlip_uniqueness` (velocity-only, over general horizons `Ico 0 (min T₁ T₂)`) | velocity **and pressure** equal on `Ico 0 T` | velocity only, `min T₁ T₂` | `PeriodicLocalTheoryAPI.velocity_unique` | **B.** `prop:local` clause is velocity uniqueness; A's pointwise pressure uniqueness is beyond it (drop). |
| singular exactly at `T` (`:666`) | `solution`; `lifespan` (`domainMaximalLifespan = ofReal T`); `maximal` (`IsMaximalDomainSolution`); `blowup` (registered `SpeedUnboundedAt`); `blowup_limsup` (`MaximalPartial.limsupLeft/speedENorm = ⊤`) | `DomainSpeedUnboundedAt`,`DomainSpeedLimsup`, `IsMaximalBoundedSolution` (predicate) | `solution`,`lifespan`,`blowup`,`blowup_limsup` (registered), **no `maximal`** | `solution`,`lifespan`,`blowup`,`blowup_limsup`,`maximal` | **B forms + a `maximal` from A (record form).** Registered `SpeedUnboundedAt`/ess-sup `blowup_limsup` (house style); add `maximal` as `IsMaximalDomainSolution` (record form over `ClassicalSolutionOmega`, not A's predicate). |

Threshold bookkeeping (`ε₀`,`eps_pos`,`eps_le_scaling`,`eps_le_cutoff`) and the three
`eq:insertion` formulas (`velocity_formula`/`pressure_formula`/`force_formula`)
mirror T18 with the un-periodized packet and the `∫_Ω` gauge.

## C. Correction/scaling threading — the T18↔T23 asymmetry (binding)

Do **not** thread a scaling or correction API. The whole-space `ScalingAPI`
(proven, `Tests/Scaling.lean:15`) and `CorrectionAPI` (inhabited, `Bindings`)
certify `scaledPacket`/`scaledForce`; the finalization **consumes** them for
`energyRate`, `forceDifference_sobolev_bound`, the cross-transport zeros, and
`force_mem`/`forceDifference_mem`, with `M=P.energyBound`, `D=P.dissipationBound`.
Only `norms : BoundedDomainNormAPI` (unregistered T22) and
`reference : ClassicalSolutionOmega` (structure exception) are threaded. This is
the exact opposite of T18, which threads the *torus* (unregistered) scaling/
correction chain. (RECONCILIATION §3 "Correction/scaling threading".)

## Proof dependencies (copied from RECONCILIATION §4)

The spec lane writes only the statement; recorded for the assembly lane:

- **T22** (`norms` parameter): `BoundedDomainNormAPI.orderZero` (`L²(Ω)` energy),
  `zeroExtensionComparison` (`eq:zero-extension`) driving `domain_zeroExt_comparison`
  and the domain force rate after time integration, `cutoffMultiplier` for the
  `s<0` `L²`-bound tail; `forceDifference_spatialSupport` supplies the fixed
  compact `K` making the constant `ε`-independent (`:661-663`).
- **Whole-space scaling/correction** (consumed, registered+inhabited):
  `scalingStatement`/`ScalingAPI` (`Tests/Scaling.lean:15`) → `energyRate`
  `(M+D)ε^{1/2}`, `forceDifference_sobolev_bound` `ε^{1/2−s}`, single-copy
  support, `blowup`/`blowup_limsup`, `force_mem`; `CorrectionAPI`/`correctionStatement`
  (`Bindings`, `Contracts/V2/CorrectionV2`) → the two `crossTransport_*` zeros,
  the `Cε^{3/2}`/`ε^{3/2−s}` correction terms, `forceDifference_mem`.
- **T11 domain analogue** (`prop:local`): `noSlip_uniqueness` from the
  difference-energy identity with vanishing boundary terms; `lifespan`/`solution`/
  `maximal` from local existence/continuation on `Ω`; `H²↪L∞` (Mathlib) for the
  `≤T` half. No registered bounded-domain local theory exists yet — the
  assembly's main construction burden.
- **`noSlip_preserved`:** `collar_agreement` + `reference.no_slip` +
  `interiorBall_in_domain` (the interior ball misses `frontier Ω`).

**`Paper1/BoundaryCorollary.lean` and corrected candidate.** The candidate
`Paper1/BoundaryCorollary.lean` (`BoundedReference:28`, `BoundedFlow:42`,
`domainForceNorm:24`, `exists_interior_noSlip_insertion:76`) has a `sorry` at
`:90` — **cited only, never imported** (rule 3). `BoundaryCorollaryCorrected.lean`
(`disjoint_frontier_of_subset_interior:19`, `InteriorNoSlipInsertionContract:28`,
`corrected_interior_noSlip_insertion:45`) is the `sorry`-free collar⇒no-slip
geometry; `LocalizationBoundary.lean` (`domainL2Sq_le_whole:64`,
`domainDissipation_le_whole:91`, the `eq:zero-extension` analytic core `:189`) and
`BoundaryReferenceRestriction.lean` (`noSlip_of_reference_and_supported_difference:76`)
are the likely proof-side reuse. None is a specification input.

## Open questions for the owner (copied from RECONCILIATION §4)

1. **Cube-free interior placement (both drafts defective).** Confirm the
   finalization introduces `DomainPlacementData` without `chartBall_in_cube`/
   `fundamentalCube` (A's origin-centering is FALSE; B's torus cube makes the
   statement vacuous off `(0,1)³`). The T23 analogue of T18's own "torus cube /
   registration" question. **[Done in this spec: `DomainPlacementData` is
   cube-free, support at `place.x₀`, domain containment via `interiorBall_in_domain`.]**
2. **Register `ClassicalSolutionOmega` + `BoundedDomainNormAPI` (T22) before T23
   assembly?** T23 threads the unregistered T22 norm layer and a new domain
   solution record; a registered `Contracts/V1` T23 cannot import `research/T22`.
   Decide whether to register T22 and a bounded-domain data contract first
   (analogue of T18's T15-registration and T19's T18-registration questions).
3. **Domain-shape encoding.** Confirm A's `IsRegularLevelDomain`
   (`∃ φ, ContDiff∞ ∧ Ω={φ<0} ∧ ∀ x∈∂Ω, fderiv φ x ≠ 0`) as the "bounded smooth
   domain" encoding (+ `IsBoxDomain` + explicit `Nonempty`), or a different
   smooth-boundary predicate. The box-vs-smooth distinction only governs the
   *assumed* reference's elliptic regularity (`:645`), but fidelity keeps the
   disjunction.
4. **Consume vs thread the whole-space insertion.** T23 = `thm:insertion` with
   the un-periodized whole-space packet localized to an interior ball. Confirm the
   assembly consumes registered whole-space `ScalingAPI`/`CorrectionAPI`/
   (`InsertionFamilyAPI`) rather than threading the torus T15/T16/T17 chain (the
   T18↔T23 asymmetry), which also removes the need for a raw threaded
   `D : CutoffData`.
5. **Pressure-gauge status and no-slip uniqueness scope.** Confirm the gauge is
   imposed by construction (`domainNormalizePressure`, B) rather than merely
   permitted (`:644` "may be"), and that `noSlip_uniqueness` is velocity-only over
   general horizons (B) — A's pointwise pressure uniqueness is beyond `prop:local`'s
   difference-energy clause.
