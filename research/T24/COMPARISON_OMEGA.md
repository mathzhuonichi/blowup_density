# Torus → Ω comparison (lane 496)

Source: reconciled `Spec.lean:1176–1333` and canonical `Multiple.lean`.
Article citations below use **revised** `03-torus.tex:511–535`; the source
record's 697–722 citations refer to the older manuscript.

There are 30 fields: retain 29 torus field names, drop `scaling`, add `no_slip`.
The research record is indexed by registered `Contracts.V1.PacketImportAPI`,
in `BlowupDensity.T24.MultipleOmega`. The canonical restatement substitutes
its velocity, pressure, force, carrier, energyBound and dissipationBound with
raw u,p,f,K,M,D and expands the packet hypotheses, as in `Multiple.lean`.
Both import canonical domain vocabulary rather than copying older T10/T15
definitions. No solution, placement, scaling API or desired conclusion is an
existence premise.

| Field / parameter | Domain change and reason |
|---|---|
| `Ω`, `hΩ` parameters | Universally prescribed `IsBoundedBoxOrSmoothDomain Ω`; mirrors the owner's T23 class. No geometry is chosen by an inhabitant. |
| `region_interior` | `closure (ball c_j ρ_j) ⊆ Ω`; no fundamental cube or lattice separation. |
| `placement` | `DomainPlacementData`; use `domainPlacementData` at the prescribed ball. The chart/time equalities remain mandatory. Its harmless stronger `2 ε² < T` threshold implies the article's separate `eps_time`. |
| `scaling` (dropped) | T15 `ScalingAPI` requires torus placement and carries periodic solutions, single-copy transfer and Haar norms. No such record is needed for un-periodised packets. Selected scales, concrete component pins and supports retain the construction data. No replacement opaque scaling premise. |
| `component` | `ClassicalSolutionOmega ν Ω 0 (scaledForce …) T`. Smoothness is the T23 open-neighborhood closed-slab convention, PDE/divergence hold in Ω, initial data on Ω, no-slip on its frontier, pressure mean over Ω. Periodicity and the torus Sobolev-path field are dropped inside this solution class. |
| `component_pin` | T15.Bridges `scaledVelocity`, and `domainNormalizePressure Ω (scaledPressure …)`. These are the un-periodised Source.PacketScaling fields consumed by I03, with start time `T − ε²`. There is no reference velocity, correction or lattice sum. The Ω-mean adjustment is necessary for the owner's solution class; it leaves the pressure gradient unchanged. Do not claim normalized pressure is supported in the ball. |
| `component_support`, `component_force_support` | Global `∀ x : Space` vanishing outside the ball; velocity on `[0,T)`, force at all real times. This stronger statement is appropriate for the un-periodised compactly supported fields; no cube restriction. |
| `assembled_force_formula` | Sum the raw scaled forces. Velocity and pressure formulas still sum the selected components, including their gauges. |
| `solution`, `force_mem` | Owner's `ClassicalSolutionOmega` and `forceClassOmega Ω`. Force smoothness on every finite closed slab and compact positive temporal support are retained; no periodicity. |
| `energy_bound` | Squared `energyEssSupOmega`: time essential supremum of physical `eLpNorm _ 2 (volume.restrict Ω)` on `(0,T)`, ≤ `ofReal (M² Σ ε_j)`. This is the L² side of registered `T04.bounded_domain_norm`, canonical `T22.BoundedDomainNormAPI.orderZero`, equating it to `domainSobolevENorm Ω 0 (restrictField Ω z)` for smooth fields on open Ω. |
| `dissipation_bound` | Squared `energyGradientOmega`: restricted space-time L² of **I02.spatialGradient**, the full Euclidean gradient, equal to `ofReal (D² Σ ε_j)`. Not the operator norm of the Fréchet derivative. Same registered I02/I03 physical gradient convention, replacing whole-space/Haar measure by restricted volume. |
| `no_slip` (added) | Explicit assembled velocity vanishing on `frontier Ω` for `[0,T)`, article 517,533; follows eventually from interior support, and is also carried by `solution`. |

All other field expressions retain the torus skeleton (with the dependent
component/placement projections now of domain type): `T_pos`, `N_pos`,
`regionRadius_pos`, `regions_disjoint`, `placement_time`, `placement_chart`,
`ε`, `eps_admissible`, `eps_time`, `assembled_velocity`,
`assembled_velocity_formula`, `assembled_pressure`, `assembled_pressure_formula`,
`assembled_force`, `solution_pin`, `rest`, `region_agreement`, `region_blowup`.
The probe checks both versions of each of these 18 shared field expressions.
`rest` remains global because these explicit packets vanish globally initially.
`SpeedUnboundedAtOn` is reused unchanged, with separate witnesses per ball.

`initialClassOmega` is used through the prescribed zero initial field and the
solution's `initial` clause; no extra initial datum is introduced.
`domainMaximalLifespan` is not a field: Proposition 3.16 asks for separate limsup
blow-up, not a new lifespan identity. Any such consequence belongs downstream.
The bounded-domain spec does not inhabit or register the API and does not close
`M316_B`; its `completion_from: [M316, B314]` remains unchanged.
