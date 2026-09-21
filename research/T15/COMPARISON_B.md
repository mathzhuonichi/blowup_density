# T15 draft B comparison — `prop:scaling`

This comparison is based only on `paper/sections/03-torus.tex:99-175`, the
reconciled T10/T13/T14 specifications, and the registered Section 4 contracts
`I01.packet` and `I03.scaling`. It does not use another T15 draft or brief.

## 1. Paper clause → Lean declaration → `I03.scaling`

| Paper clause | Draft B declaration | Registered `I03.scaling` counterpart |
|---|---|---|
| Choose `K_* ⊇ K ∪ pr_x supp F`, `x₀`, and a sufficiently small common scale (`:101-106`) | `ScalingAPI.supportCarrier`, `supportCarrier_compact`, `packetCarrier_subset`, `forceProjection_subset`, `supportRadius`, `supportRadius_subset`, `x₀`, `chartRadius`, `chartBall_subset`, `ε₀` | `ScalingAPI.carrier_subset`, `ε₀`, `eps_pos`, `eps_le_one`, `eps_time`, `eps_space`; I03 does not carry the spatial projection of `supp F` |
| `t_ε=T-ε²` (`:106`) | `scaledStartTime` | Inlined in `scaledPacket`, `Contracts.V1.scaledPressure`, and `Contracts.V1.scaledForce` |
| `U_ε=ε⁻¹U((x-x₀)/ε,(t-t_ε)/ε²)` (`:112-114`) | `scaledVelocity` | `Contracts.V1.scaledPacket` |
| `P_ε=ε⁻²P((x-x₀)/ε,(t-t_ε)/ε²)` (`:115-116`) | `scaledPressure` | `Contracts.V1.scaledPressure` |
| `F_ε=ε⁻³F((x-x₀)/ε,(t-t_ε)/ε²)` (`:117-118`) | `scaledForce` | `Contracts.V1.scaledForce` |
| Place in `B`, periodize, and retain one copy per cell (`:120`) | `periodizedScaledVelocity`, `periodizedScaledPressure`, `periodizedScaledForce`; the three `...Periodization_summable` and three `..._singleCopy` fields | No counterpart: I03 deliberately works on `ℝ³` without periodization |
| The rescaled force remains in the torus force class (`:108-120`, implicit in the smooth compact construction) | `periodizedForce_mem : MemForceT ...` | Whole-space smooth/support facts are inherited from `PacketAPI`; I03 has no separate force-membership field |
| Same-viscosity periodic equation, divergence free, zero initial data (`:122-123,141`) | `solution : ∃ S : ClassicalSolutionT ν 0 F_ε T, S.velocity=... ∧ S.pressure=...` | `scaledEquation` and `scaledDivergenceFree`; zero initial behavior is inherited from the packet’s quiet interval rather than exported as an I03 field |
| Unbounded speed at `T` (`:123,142-143`) | `unboundedSpeed : SpeedUnboundedAt T ...` | `scaledBlowup`, with the same `∀ K>0, ∀ δ>0, ∃ t,x` predicate |
| A spatially constant pressure adjustment enforces mean zero (`:123`) | `normalizedScaledPressure`, `pressureSlice_integrable`, `pressureNormalization` | No Euclidean counterpart; I03 uses the raw scaled pressure |
| `‖U_ε‖_{L∞L²}=ε^{1/2}M` (`:125-126`) | `energySlices_memLp`, `packetEnergyIdentity` using `energyEssSupT` | `packetEnergyIdentity` using `Data.energyEssSup` |
| `‖∇U_ε‖_{L²L²}=ε^{1/2}D` (`:127-128`) | `energySlices_memLp`, `packetDissipationIdentity` using `energyGradientT` | `packetDissipationIdentity` using `Data.energyGradient` |
| `‖F_ε‖_{L^qL^p}=ε^{α(p,q)}‖F‖`, `1≤p,q≤∞` (`:129-132,148-149`) | `scalingExponent`, `mixedLebesgueENormT`, `mixed_memLp`, `packetMixedScaling` | `alpha` and `packetMixedScaling` using `Data.mixedLebesgueENorm` on both sides |
| `‖F_ε‖_{L¹H^s(T³)}≤C_s(ε^{1/2}+ε^{1/2-s})`, `0≤s≤1` (`:133-137,150-158`) | data field `sobolevConst`, then `sobolevConst_nonneg`, `forceSobolev_memLp`, `packetSobolevBound`; `localization : T13.Draft.LocalizationAPI` is carried and its `localization`/endpoint fields are cited | Closest field is `packetPositiveScaling` at `q=1`; it is a whole-space estimate and does not contain T13 localization |
| In particular, convergence to zero for every `s<1/2`, including negative `s` (`:138,158`) | separate concrete proposition `SubcriticalForceConvergence`; deliberately not a `ScalingAPI` field | Closest are `forceLowOrderBound` and `forceConvergence`; I03’s latter concerns the packet plus correction, not the packet alone |

## 2. Representation choices

### Periodization and the single-copy condition

The draft uses the literal lattice sum

`∑' n : Fin 3 → ℤ, f(t, x - latticeVector n)`.

This choice states an actual periodic physical field and matches T13’s
`periodize`. It also exposes a possible `tsum` totalization trap, so the API
records summability for velocity, pressure, and force. On the fixed cube it
records pointwise equality with the zero-lattice summand.

The paper’s geometric condition is rendered by choosing the localization ball
to be centered at `x₀`, placing `K_*` in `ball 0 R_*`, and imposing
`ε R_* < chartRadius`. Together with
`closure (ball x₀ chartRadius) ⊆ interior fundamentalCube`, this yields
`x₀ + ε K_*` inside a single coordinate cell. Centering the smaller ball at
`x₀` is a harmless specialization of the paper’s wording “fix `x₀ ∈ B`”; it
keeps the support-radius implication explicit.

### Scale range and quantifier order

One threshold `ε₀` is chosen before all conclusions. Every scale-dependent
field has `∀ ε ∈ Ioc 0 ε₀`. The record also stores `0 < ε₀`, `ε₀ ≤ 1`,
`2 ε² < T`, and `ε R_* < chartRadius`. Thus `t_ε>0`, and the positive-time
norm sees the entire transformed force support. The constants `C_s` are the
function-valued data field `sobolevConst : ℝ → ℝ`, chosen before `ε`, rather
than an existential nested after `ε`.

### Norm codomains and honest membership

The following quantities are `ℝ≥0∞`:

- `energyEssSupT` and `energyGradientT`;
- `mixedLebesgueENormT` and `Data.mixedLebesgueENorm`;
- `forceSobolevENormT` and the T10 pointwise Sobolev norm.

Accordingly the finite real scale factors are inserted with `ENNReal.ofReal`.
The exponent uses `p q : ℝ≥0∞`; `toReal ⊤ = 0` implements `1/∞=0`.

The identities do not rely on totalized integrals accidentally returning a
junk value. `energySlices_memLp` records spatial `L²` membership;
`mixed_memLp` exhibits finite Bochner paths on both sides of the exact mixed
identity; `forceSobolev_memLp` exhibits a finite T10 Fourier-data path, whose
`IsPeriodicDatum` includes the lead-amendment Haar-integrability conjunct;
`pressureSlice_integrable` makes pressure normalization honest. Smooth compact
support should prove all of these facts, but the contract records them rather
than hiding that implementation work.

### PDE and pressure

The PDE clause is a pinned existential `ClassicalSolutionT`, not a weaker
pointwise-only conjunction. This gives T18 the periodicity, regularity,
incompressibility, zero initial value, momentum equation, pressure-gradient
membership, and gauge in its reconciled consumer shape. The raw periodized
pressure is normalized only after the lattice sum; subtracting its spatial
mean is constant in `x`, so it preserves the momentum equation.

## 3. Ambiguities and fidelity decisions

1. `research/T13/Spec.lean` currently declares namespace
   `BlowupDensity.T13.Spec`, while the T15 lane brief requests copied names in
   `BlowupDensity.T13.Draft`. Draft B follows the lane brief and otherwise
   copies the selected declarations. Registration should settle the final
   namespace and delete this temporary copy.
2. The paper says “fix `x₀ ∈ B`” but does not insist that `B` be centered at
   `x₀`. The centered sub-ball used here is stronger and is the cleanest exact
   way to turn `εR_*<r` into the single-copy inclusion.
3. The source packet’s `K` controls only velocity and pressure. The force may
   have a larger spatial projection, so Draft B carries a genuine `K_*` and
   does not repeat I03’s known omission of `pr_x supp F`.
4. The paper writes real-valued norms, while T10’s total norms are `ℝ≥0∞`.
   `ENNReal.ofReal` is therefore unavoidable on the right sides. Positivity of
   `M` and `D` is derivable from `PacketAPI.energy_isLUB` and
   `dissipation_eq`; it is not duplicated as T15 data.
5. At `p=∞` or `q=∞`, the mixed-norm formula is represented by `ENNReal`
   exponents and `toReal`, following I03. No separate endpoint cases are added.
6. `eq:packetHs` is stated only for `0≤s≤1`. The paper’s negative-order
   convergence is separate: it follows from the order-zero bound and Sobolev
   monotonicity, not from extending the localization inequality to negative
   homogeneous orders.
7. The fundamental cube is the closed `[0,1]³`, while `torusLift` chooses
   `(0,1]³` representatives. The support lies strictly in the interior, so the
   boundary discrepancy is pointwise harmless for the single-copy fields and
   null for all Haar norms.

## 4. Needs a lemma

1. Definitional bridges from the three explicit T15 rescalings to
   `Contracts.V1.scaledPacket`, `scaledPressure`, and `scaledForce` for `ε≠0`.
2. Compact projection: from `PacketAPI.force_support`, construct compact
   `K_*` containing `P.carrier` and `pr_x (tsupport P.force)`, then choose
   `R_*>0` with `K_* ⊆ ball 0 R_*`.
3. Interior geometry: choose `x₀` and `r>0` with
   `closure (ball x₀ r) ⊆ interior fundamentalCube`, and choose one `ε₀`
   satisfying both time and space smallness conditions.
4. Local finiteness/summability of the lattice sum, periodicity of the sum, and
   the pointwise single-copy equality from `εR_*<r`.
5. Periodization preserves smoothness on the single-copy support, including at
   cell boundaries; derive `MemForceT` and the `ClassicalSolutionT` regularity
   fields.
6. Pressure normalization: raw slice integrability, zero mean after
   subtraction, preservation of the pressure gradient, and preservation of the
   residual equation.
7. Exact torus `L²` and gradient identities from T13’s `endpoint_zero` and
   `endpoint_one`, plus the time change of variables and the exact packet `IsLUB`
   argument needed for the essential supremum equality.
8. A torus mixed-norm single-copy lemma for all `1≤p,q≤∞`, including both
   essential-supremum endpoints, producing the `MemLp` paths as well as the
   equality.
9. For `0<s<1`, integrate `LocalizationAPI.localization` in source time with
   the exact homogeneous scaling. Treat `s=0` and `s=1` through the endpoint
   fields. Assemble vector components without changing the exponents.
10. Datum-path construction: convert the smooth periodic force slices into
    T10 `PeriodicSobolev` data, prove strong measurability, and prove `MemLp`.
11. Negative-order monotonicity
    `forceSobolevENormT 1 s f ≤ forceSobolevENormT 1 0 f` for `s<0` under the
    amended datum vocabulary.
12. Derive `SubcriticalForceConvergence`: use item 11 for `s<0`,
    `packetSobolevBound` for `0≤s<1/2`, and transfer the real-power limit through
    `ENNReal.ofReal` and the right-neighborhood filter.

## 5. Existing `Paper1/` implementation candidates (not imported)

- `PeriodicScalingBounds.periodic_interpolation_of_endpoint_energies` and
  `periodic_interpolation_of_endpoint_bounds`: interpolate periodic `H⁰/H¹`
  endpoint information, but explicitly do not prove localization.
- `PeriodicPacketEndpointRates.packet_scalar_H0_L1_endpoint_bound` and
  `packet_scalar_H1_L1_endpoint_bound`: whole-space component endpoint rates.
- `PeriodicPacketEndpointRates.packet_vector_H0_L1_endpoint_bound` and
  `packet_vector_H1_L1_endpoint_bound`: vector reassembly at the two endpoints.
- `ScalingLimits.sobolev_error_tendsto_zero`: the proof pattern for the scalar
  limit. Its existing exponents are the later insertion rates
  `ε^{1/2-s}+ε^{3/2-s}`, so T15 still needs the simpler companion for
  `ε^{1/2}+ε^{1/2-s}`.
- `ScalingLimits.energy_error_tendsto_zero`: later T18 energy convergence.
- `ScalingLimits.mixedExponent`, `mixedExponent_pos_iff`, and
  `mixed_error_tendsto_zero`: exponent arithmetic and mixed-norm decay regions.

These candidates cover endpoint bounds and scalar limits. None supplies the
new T13 localization-to-periodic-norm bridge, the single-copy lattice theorem,
or the T10 datum-path witnesses required by this specification.
