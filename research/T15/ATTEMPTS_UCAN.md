# T15 U-CAN — raw packet mapping and conformance notes

Lane 384 replaces the contract structures in the T15 statement layer with raw
canonical parameters.  It does not prove any of the 21 `ScalingAPI` fields.
All source-packet assumptions occur as premises of `scalingStatement`; no
assumption is hidden in a placeholder proposition.

## Packet data mapping

| Spec projection | Canonical raw parameter | Where it appears |
|---|---|---|
| `P.velocity` | `u : VelocityField` | placement parameter; scaled velocity, solution, blowup, energy fields |
| `P.pressure` | `p : PressureField` | placement parameter; scaled/periodized/normalized pressure and solution |
| `P.force` | `f : VelocityField` | placement support projection; force periodization and all force norms |
| `P.carrier` | `K : Set Space` | `PlacementData.carrier_subset` and the placement parameter of `ScalingAPI` |
| `P.energyBound` | `M : ℝ` | `packetEnergyIdentity` |
| `P.dissipationBound` | `D : ℝ` | `packetDissipationIdentity` |
| `P.quietTime` | `τ : ℝ` | raw source premise block of `scalingStatement` |

`PlacementData P` becomes `PlacementData u p f K`.  Only `f` and `K` occur
in its field types, but retaining all four physical fields makes its parameter
order identical to the downstream raw scaling package and avoids a second
placement adapter in T17/T18.

## `PacketAPI` clause mapping

The 26 propositional fields are explicit arrows of `scalingStatement` in the
same order as `Contracts.V1.PacketAPI`.  `hν` is simultaneously the outer
positive-viscosity premise and the raw image of `P.viscosity_pos`.

| `PacketAPI` field | Raw premise in `scalingStatement` | T15 role |
|---|---|---|
| `viscosity_pos` | `hν : 0 < ν` | fixed positive viscosity |
| `velocity_smooth` | `ContDiffOn ℝ ∞ u preSingularDomain` | scaled velocity regularity/support transport |
| `pressure_smooth` | `ContDiffOn ℝ ∞ p preSingularDomain` | scaled pressure regularity |
| `force_smooth` | `ContDiff ℝ ∞ f` | periodized force and honest Bochner paths |
| `force_support` | `CompactPositiveTimeSupport f` | force time support and spatial projection compactness |
| `carrier_compact` | `IsCompact K` | placement/support transport |
| `velocity_support` | `∀ t ∈ Ico 0 1, tsupport (u t) ⊆ K` | single-copy velocity |
| `pressure_support` | `∀ t ∈ Ico 0 1, tsupport (p t) ⊆ K` | single-copy pressure |
| `zero_initial_velocity` | `∀ x, u (0,x) = 0` | zero initial datum |
| `divergence_free` | `∀ t ∈ Ico 0 1, ∀ x, spatialDivergence u t x = 0` | source incompressibility |
| `navier_stokes` | `∀ t ∈ Ioo 0 1, ∀ x, navierStokesResidual ν u p t x = f (t,x)` | source momentum equation |
| `speed_unbounded` | `SpeedUnboundedAtOne u` | `unboundedSpeed` transport |
| `square_integrable` | `∀ t ∈ Ico 0 1, SquareIntegrableAtTime u t` | honest source energy slices |
| `energy_isLUB` | `IsLUB ((sqrt ∘ l2Sq u) '' Ico 0 1) M` | exact energy scaling coefficient |
| `dissipation_integrable` | `IntegrableOn (dissipation u) (Ioo 0 1)` | honest source dissipation |
| `dissipation_eq` | `D = sqrt (∫ t in Ioo 0 1, dissipation u t)` | exact dissipation coefficient |
| `quiet_pos` | `0 < τ` | nondegenerate quiet interval |
| `quiet_lt_one` | `τ < 1` | quiet interval lies before blowup |
| `force_quiet` | `∀ t ∈ Icc 0 τ, ∀ x, f (t,x) = 0` | smooth inactive history |
| `velocity_quiet` | `∀ t ∈ Icc 0 τ, ∀ x, u (t,x) = 0` | smooth zero-past velocity |
| `pressure_quiet` | `∀ t ∈ Icc 0 τ, ∀ x, p (t,x) = 0` | smooth zero-past pressure |
| `force_zero_nonpos` | `∀ t ≤ 0, ∀ x, f (t,x) = 0` | force extension convention |
| `velocity_extension_smooth` | `ContDiffOn ℝ ∞ (zeroPastField u) (Iio 1 ×ˢ univ)` | scaled velocity smoothness across the start time |
| `pressure_extension_smooth` | `ContDiffOn ℝ ∞ (zeroPastField p) (Iio 1 ×ˢ univ)` | scaled pressure smoothness across the start time |
| `extension_navier_stokes` | zero-past residual identity for every `t < 1` | rescaled momentum equation, including inactive past |
| `extension_divergence_free` | zero-past divergence identity for every `t < 1` | rescaled incompressibility, including inactive past |

## `PacketEnergyAPI` clause mapping

| Spec field | Raw premise |
|---|---|
| `P.energy.energy_le_work` | the exact `l2Sq + 2ν∫dissipation ≤ 2∫sqrt(l2Sq f)·accumulatedForce f` relation on `Ico 0 1` |
| `P.energy.work_eq_square` | the exact work integral `= accumulatedForce f t ^ 2` on `Ico 0 1` |

These two premises are retained even though the displayed T15 energy scaling
identities use the sharper `energy_isLUB` and `dissipation_eq` fields directly.
This makes the raw statement exactly reversible to a full
`PacketImportAPI`, rather than silently weakening its source object.

## Structure and field mapping

| Spec structure | Canonical structure | Mapping |
|---|---|---|
| `PlacementData P.toPacketAPI` (17 fields) | `PlacementData u p f K` (17 fields) | `placementOfSpec` / `placementToSpec`, fieldwise; both round trips are `rfl` |
| `ScalingAPI P place` (21 fields) | `ScalingAPI (ν := ν) u p f K M D place` (21 fields) | `ofSpec` / `toSpec`, all fields named explicitly; both round trips proved |

The rescaling bridge list is
`scaledStartTime`, `scaledSourcePoint`, `scaledVelocity`, `scaledPressure`,
`scaledForce`, the three `periodizedScaled*` families,
`normalizedScaledPressure`, and `alphaT`.  All ten bridges are `rfl`; the four
raw rescaling families (velocity/pressure/force/normalized pressure) are the
ones whose argument changes visibly from `P` to a raw field.

## Checks while developing

- The canonical module builds from `verification/`.
- The standalone probe elaborates with no output.
- The axiom audit reports exactly the standard
  `[propext, Classical.choice, Quot.sound]` footprint for every canonical
  declaration.
