# T23 Draft A comparison

This draft transcribes `cor:boundary` (`paper/sections/03-torus.tex:632-667`).
The T18 vocabulary is copied verbatim in `DraftA.lean` because the bounded
construction reuses the insertion displays; the T22 restriction and zero
extension vocabulary is copied verbatim as well.  The `BoundaryCorollary`
implementation candidate is cited only and is not imported (it contains the
known `sorry` at line 90).

## Paper clause to Lean field

| Paper clause | Draft A field/definition | Section 4 counterpart or difference |
|---|---|---|
| bounded box or bounded smooth domain (632--634) | `IsBoxDomain`, `IsRegularLevelDomain`, `IsBoundedBoxOrSmoothDomain`, `domain_shape` | torus-only domain hypothesis; Section 4 `InsertionFamilyAPI` has no Ω |
| ν>0 and target T>0 (632--634) | `viscosity_pos`, `time_pos` | `InsertionFamilyAPI` has the same viscosity input and correction time |
| compatible margin δ>0 (633--635) | `delta_pos`; statement hypothesis `0 < δ` | R42 `ScalingAPI`/`CorrectionAPI` margin |
| smooth reference velocity on the closed slab, with neighborhood convention (635--639) | `SmoothOnClosedDomainSlab`, `reference_velocity_smooth` | R42 `reference` is `ClassicalSolutionR`; closed-domain neighborhood is torus-only |
| smooth reference pressure on the slab (635--639) | `reference_pressure_smooth` | R42 `reference_pressure`; no boundary restriction there |
| force smooth on every finite slab and compact in positive time (635--637) | `reference_force_smooth`, `CompactPositiveTimeSupportOnDomain`, `DomainForceClass`, `reference_force_mem` | R42 `MemForceCompact`; Draft A keeps the bounded-domain wording |
| initial value in Ω (635--637) | `initial_datum` | R42 `reference.initial` is whole-space |
| incompressibility in Ω (635--637) | `reference_divergence` | R42 `reference.divergence` |
| momentum equation in Ω (635--637) | `reference_momentum` | R42 `reference.momentum` |
| no-slip reference boundary values (635--637) | `reference_no_slip` | torus-only; R42 has no boundary condition |
| optional zero-mean pressure normalization (637--638) | `domainMean`, `reference_pressure_gauge` | torus `PressureGaugeT`; Section 4 compact pressure gauge differs |
| fixed compact interior support region (639--641) | `interior_region`, `interior_region_compact`, `interior_region_subset` | R42 `ball`/`CorrectionAPI.x₀,r`; bounded version is explicitly `K ⊂ interior Ω` |
| fixed boundary collar preserved (642--644) | `collar`, `collar_open`, `collar_covers_boundary`, `collar_disjoint_interior`, `boundary_collar_preserved` | torus-only; no Section 4 counterpart |
| one sufficiently-small ε interval (642--643) | `ε₀`, `eps_pos`, every scale field uses `ε ∈ Ioc 0 ε₀` | R42 `ε₀`, `eps_pos`, `eps_le_scaling` |
| insertion displays `uε=v+wε+Uε`, `pε=π+Pε`, `gε=g+Hε+Fε` (644--646) | `backgroundCorrection`, `packetVelocity`, `packetPressure`, `packetForce`, `correctionForce`, `velocity_formula`, `pressure_formula`, `force_formula` | R42 `*_formula`; pressure gauge is the bounded-domain choice |
| inserted force is in the force class (647--648) | `force_mem` | R42 `forceDifference_compact` plus force class |
| force difference remains smooth and positive-time compact (647--648) | `forceDifference_mem` | R42 `forceDifference_compact`, `forceDifference_ball` |
| inserted velocity/pressure smooth on `[0,T)` (647--649) | `velocity_smooth`, `pressure_smooth` | R42 same fields, with `Ico` whole-space slab |
| initial velocity unchanged (647--649) | `initial` | R42 `initial` |
| incompressibility and exact equation in Ω (647--650) | `incompressible`, `momentum` | R42 `incompressible`, `momentum`; Ω restriction is torus-only |
| earlier history unchanged through `T−2ε²` (647--651) | `history` | R42 `history` |
| no-slip inserted solution (647--651) | `no_slip` | torus-only boundary clause |
| insertion agrees with reference in a fixed boundary collar (642--644) | `boundary_collar_preserved` | torus-only |
| bounded classical solution witness (647--650) | `IsBoundedClassicalSolution`, `solution` | R42 `InsertionLifespanV2API.solution`; bounded predicate adds no-slip and domain energy guards |
| maximal identification (647--651) | `boundedMaximalLifespan`, `IsMaximalBoundedSolution`, `maximal`, `lifespan` | R42 `maximal`/lifespan package; bounded maximal lifespan is new |
| unbounded speed as `t↑T` (647--651) | `DomainSpeedUnboundedAt`, `DomainSpeedLimsup`, `blowup`, `blowup_limsup` | R42 `SpeedUnboundedAt`, `blowup_limsup`; Ω-local norm is new |
| divergence-free velocity difference (653--655) | `velocityDifference_divFree` | R42 exported `velocityDifference_divFree` |
| support diameter `O(ε)` and interior placement (653--655) | `difference_support_radius`, `difference_support_radius_pos`, `velocityDifference_support`, `difference_support_interior` | R42 `velocityDifference_support`; bounded field records interior inclusion |
| domain energy uses `L²(Ω)` and gradient (656) | `domainEnergyENorm`, `DomainEnergySlicesMemLp`, `energy_slices_memLp`, `energyRate` | R42 `energyRate` with whole-space `energyENorm`; Ω and zero-extension bookkeeping is new |
| constants/data in the energy estimate (656) | `energyBound`, `dissipationBound`, `correctionEnergyConst`, `energy_constants_nonneg` | R42 constants come from `PacketAPI`/`CorrectionAPI`; Draft A carries them as Type data |
| `L¹_tH^s(Ω)` force paths, `0≤s<1/2` (657--660) | `IsDomainSobolevPath`, `domainForceSobolevENorm`, `MemDomainForceSobolev`, `forceDifference_sobolev_memLp` | R42 `forceDifference_sobolev_memLp` uses whole-space/torus vocabulary |
| subcritical force rate (657--660) | `forceDifference_sobolev_bound` | R42 `forceDifference_sobolev_bound`; Ω norm is new |
| convergence remains `s<1/2` (660--661) | `forceDifference_sobolev_tendsto` | R42 `forceConvergence` has the critical-order formulation |
| negative-order tail and summability guard (660--661) | `forceDifference_negativeSobolev_memLp`, `forceDifference_negativeSobolev_tendsto` | R42 `negative_s_memLp` and negative convergence |
| restriction versus zero-extension norms for every real s, C independent of ε (660--662) | `zeroExtension_comparison`, `zeroExtension_sobolev_memLp` | T22 `BoundedDomainNormAPI.zeroExtensionComparison`; this is its time-integrated consumer |
| uniqueness from no-slip difference energy; boundary terms vanish (666--667) | `noSlip_uniqueness` | torus-only; R42 uniqueness is whole-space/local theory |

`boundaryInsertionStatement` follows the paper order: Ω and its geometry,
ν, `(a,g,T,δ,v,π)`, the positive margin, force/reference regularity, the
equation, initial value, no-slip boundary data, pressure gauge, and finally
`Nonempty (BoundaryInsertionAPI ...)`.

## Choices and ambiguities

* `IsRegularLevelDomain` is a concrete regular-level-set encoding of “smooth
  domain”; boxes use coordinate intervals.  This avoids an unconstrained
  proposition parameter while keeping the paper's disjunction visible.
* `SmoothOnClosedDomainSlab` explicitly quantifies an open neighborhood, so
  smoothness at box edges/corners is not silently replaced by an open-slab
  assertion.
* `domainSobolevENorm` is T22's quotient norm.  `domainForceSobolevENorm`
  takes an infimum over measurable coefficient paths, while `MemDomainForceSobolev`
  is the finite-path guard.  Whole-space zero extensions have a separate
  `MemWholeSpaceSobolev` guard.
* `boundedMaximalLifespan` uses an `ENNReal` supremum over `Nonempty` bundled
  solution witnesses.  No real `sSup` or junk zero is used.
* The pressure field is normalized by `domainMean`; the corollary permits this
  gauge but does not require a particular pressure formula beyond the insertion
  display and the gauge field.
* Mixed `L^q_tL^p_x` scaling fields from T18 are torus/periodization clauses,
  not asserted by `cor:boundary`; the bounded result retains the force Sobolev
  clauses explicitly named in the corollary.

## Needs-a-lemma list

The eventual proof consumes the following registered or copied interfaces:

1. T22 `BoundedDomainNormAPI.orderZero`, `cutoffMultiplier`, and
   `zeroExtensionComparison`, plus the copied `restrictField`, `zeroExtension`,
   and `IsCutoffDatum` definitions.
2. T18 insertion formulas, support and divergence fields, and its packet and
   correction constants (`PeriodicInsertionAPI.velocity_formula`,
   `force_formula`, `velocityDifference_support`, `energyRate`, and the
   Sobolev/mixed guards).  The bounded proof replaces periodized norms by the
   fixed interior zero extension.
3. T11 `ClassicalSolutionT`, `maximalLifespanT`, `IsMaximalPeriodicSolution`,
   and `PeriodicLocalTheoryAPI`/`PeriodicContinuationH3API` APIs for local
   existence, continuation, and maximal identification; the bounded proof
   needs their no-slip-domain analogues.
4. T12 calculus/embedding facts: the `H² → L∞` bound used for the lifespan
   contradiction and the difference-energy estimate on Ω.
5. The T20 critical package is not consumed by this corollary; only its
   continuation criterion is relevant if the bounded local theory is obtained
   through the critical route.
6. Boundary bookkeeping lemmas: support disjoint from `frontier Ω` implies
   no-slip (`BoundaryReferenceRestriction.noSlip_of_reference_and_supported_difference`),
   and uniqueness by the no-slip difference-energy calculation.

## Implementation candidates

The candidate declarations, inspected but not imported, are:

```text
formalization/NSFormalization/Paper1/BoundaryCorollary.lean:
15 IsDomainExtension
20 domainSobolevNorm
24 domainForceNorm
28 BoundedReference
42 BoundedFlow
54 noSlip_of_boundary_agreement
64 bounded_energy_restriction
76 exists_interior_noSlip_insertion   -- contains sorry at :90; cite only

formalization/NSFormalization/Paper1/BoundaryAnalyticBridge.lean:
22 BoundedFlowData
37 boundedFlow_of_data
48 ExplicitInsertionFlowBinding
57 reference_supported_noSlip_on_horizon

formalization/NSFormalization/Paper1/BoundaryReferenceRestriction.lean:
12 boundedFlow_of_reference
40 noSlip_of_supported_difference
58 tsupport_difference_subset
76 noSlip_of_reference_and_supported_difference
108 reference_noSlip_on_horizon
126 noSlip_of_horizon_support

formalization/NSFormalization/Paper1/BoundarySupportComposition.lean:
13 noSlip_of_composed_supported_differences
```

`BoundaryCorollary.lean` is deliberately absent from the imports of
`DraftA.lean`; the candidate's remaining theorem is an implementation gap,
not a specification axiom.
