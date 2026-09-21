# T15 reconciled comparison — `prop:scaling`

This comparison merges blind draft A (lane 291), blind draft B (lane 292), and
the binding rulings in `research/T15/RECONCILIATION.md`.  The statement covers
`paper/sections/03-torus.tex:101-159`; the torus force-class and classical
solution vocabulary also cites `paper/sections/02-preliminaries.tex`.

## Paper clause → Lean field, provenance, and ruling

| Paper clause | Reconciled declaration / field | Draft A provenance | Draft B provenance | Ruling |
|---|---|---|---|---|
| Choose one compact `K_*⊇K∪pr_x(supp F)`, chart ball, `x₀∈B`, `T`, and one scale range; `2ε²<T`, `x₀+εK_*⊂B` (`03-torus.tex:101-107`) | `PlacementData`: A's 17 fields `T` through `eps_space`, passed as a parameter to `ScalingAPI` | Separate shared parameter record with literal set containment | Eighteen geometry fields inlined into `ScalingAPI`, with a radius inequality | A. T15, T17, and T18 must share definitionally the same placement data. B's support radius is left as a derived implementation convenience, not primitive data. |
| `t_ε=T-ε²` and the three formulas of `eq:scaling` (`:106,108-118`) | `scaledStartTime`, `scaledSourcePoint`, `scaledVelocity`, `scaledPressure`, `scaledForce` | `packetTimeShift` plus reusable `scaledSourcePoint` | Name `scaledStartTime`; source point inlined | B's start-time name and A's reusable source point. The inverse-scale spellings are definitionally equal to registered `scaledPacket`, `scaledPressure`, and `scaledForce`; all three `rfl` checks elaborate. |
| Place in `B`, periodize, retain one support copy (`:120`) | explicit `periodizedScaledVelocity/Pressure/Force`; `velocity_summable`, `pressure_summable`, `force_summable`; three `*_singleCopy` fields | Literal lattice sums and single-copy equalities; no summability guards; force restricted to `t>0` | Literal lattice sums, three summability guards, force equality for every real `t` | B's guards and all-time force equality; field names follow reconciliation §3. The guards exclude nonsummable-`tsum` junk. |
| Use Lemma 3.2 localization to obtain the periodic `H^s` estimate (`:22-98,150-158`) | `localization : T13.Spec.LocalizationAPI` | Unused proof parameter | Record field | B. A's parameter did not constrain any conclusion. |
| The periodized force stays in `F_T` (`:108-120`; `02-preliminaries.tex:10,23-26`) | `force_mem` | `force_mem` | `periodizedForce_mem` | Keep under the reconciled name `force_mem`; this is an extra downstream-consumed class fact. |
| Same-viscosity periodic equation, incompressibility, regularity, zero initial data, periodicity, and mean-zero pressure (`:122-123,141`; `02-preliminaries.tex:28-36,75-115`) | `solution : ∀ ε…, ∃ S : ClassicalSolutionT ν 0 F_ε T, S.velocity=U_ε^per ∧ S.pressure=p_ε` | Eight separate pointwise fields | One pinned classical-solution witness | B. The pinning equations prevent substitution and the bundled object is the shape T11/T18 consume. |
| A spatially constant adjustment gives the mean-zero pressure (`:123`) | `normalizedScaledPressure` definition; `pressureSlice_integrable`; the gauge is carried by `solution` | `pressure_adjustment_constant` plus an unguarded `pressure_gauge` | `pressureSlice_integrable` plus `pressureNormalization` (formula and gauge conjuncts) | Keep the integrability guard and the gauge inside `ClassicalSolutionT`; drop both definitionally true adjustment/formula fields. The exact normalization formula has an elaborating `rfl` check. |
| Unbounded speed at `T` (`:123,142-143`) | `unboundedSpeed : SpeedUnboundedAt place.T U_ε^per` | `speed_unbounded` | `unboundedSpeed` | B's reconciled field name, registered predicate unchanged. |
| Honest energy slices for `eq:packetEscale` (`:125-128`) | `energySlices_memLp` | `energy_finite` only | slice-wise `MemLp` for velocity and full gradient | B. Drop A's derivable finiteness conjunction; retain the strong measurability/integrability guard. |
| `‖U_ε‖_{L∞L²}=ε^{1/2}M` (`:125-126,145`) | `packetEnergyIdentity`, `M=P.energyBound` | Same equality | Same equality | Agreement; equality in `ℝ≥0∞`, guarded by `energySlices_memLp`. |
| `‖∇U_ε‖_{L²L²}=ε^{1/2}D` (`:127-128,145-146`) | `packetDissipationIdentity`, `D=P.dissipationBound` | Same equality | Same equality | Agreement; equality in `ℝ≥0∞`, guarded by `energySlices_memLp`. |
| `α(p,q)=-3+3/p+2/q` and exact mixed scaling for all `1≤p,q≤∞` (`:129-133,148-149`) | `alphaT`, `mixed_memLp`, `packetMixedScaling` | `alphaT`, honest whole-space/torus paths, exact identity | Same content under `scalingExponent` | A's `alphaT` name, B's `mixed_memLp` name. Formula is token-identical to registered `alpha` and its `rfl` check elaborates. |
| One positive `C_s` fixed before scale (`:133-136`) | data field `sobolevConst`, then `sobolevConst_pos` | strict positivity | nonnegativity | A. Strict positivity on `0≤s≤1`. |
| Honest `L¹_tH^s(T³)` path (`:133-138,150-158`) | `forceSobolev_memLp` | `sobolev_mem` | `forceSobolev_memLp` | B's reconciled name. Registered `IsPeriodicDatum` supplies the Haar-integrability conjunct. |
| `‖F_ε‖_{L¹H^s}≤C_s(ε^{1/2}+ε^{1/2-s})`, `0≤s≤1` (`:133-137,150-158`) | `packetSobolevBound` | Same bound | Same bound | Agreement; guarded by `forceSobolev_memLp`. |
| “In particular” force convergence (`:138,158`) | `forceConvergence` field | Separate `ForceConvergesBelowCritical` definition | Separate `SubcriticalForceConvergence` definition | Promote to a field. Per the binding lane instruction its exact shape is `∀ q : ℝ≥0∞, (q=1 ∨ q=2) → ∀ s, s<criticalOrder q.toReal → Tendsto …`; see the first owner question below about the manuscript/reconciliation prose, which writes only the `q=1` specialization. |
| Proposition-level existence for the caller's data | `scalingStatement`: `∀ 𝔉 ν hν place, Nonempty (ScalingAPI (𝔉.select ν hν) place)` | No existential form | Existential whose equality pinned only proof-irrelevant localization data | B's existential shape, with A's placement data pinned as a parameter. No proof-irrelevant equality is used. |

## Vocabulary and definitional checks

The registered T10 data layer is imported from
`Contracts.V1.TorusData`; no registered torus-data name is copied.  The
unregistered T10 solution-class declarations, the T13 localization block, and
the T14 packet blocks are delimited verbatim copies with source-line markers.

The spec contains elaborating `example … := rfl` checks for:

- `CompletedDense = CompletedDenseVia … (IsSobolevPath …)`;
- `CompletedDenseHomogeneous = CompletedDenseVia … (IsHomogeneousPath …)`;
- each of the three explicit rescalings against the registered I03 definitions;
- the pressure-normalization formula that was dropped as a field;
- `alphaT = Contracts.V1.alpha`.

## Proof dependencies

**Needs a lemma** (union of A 1-12 and B 1-12, deduped): (1) definitional bridges from the three T15 rescalings to `Contracts.V1.scaledPacket`/`scaledPressure`/`scaledForce` for `ε ≠ 0`, and `rfl` bridges for every copied declaration; (2) construct compact `K_* ⊇ P.carrier ∪ pr_x (tsupport P.force)` (`PacketAPI.force_support` gives `HasCompactSupport`, so the projection is compact) and a chart ball with `closure ⊆ interior Q`; (3) scaled-support placement: each slice of `U_ε,P_ε,F_ε` is supported in `x₀+εK_* ⊆ B`; (4) local finiteness/summability of the lattice sum, its unit periodicity, and the single-copy equality on `Q`; (5) periodization commutes with every derivative in `navierStokesResidual`, including the nonlinear term and across cell boundaries; (6) pressure normalization: slice integrability, zero mean, unchanged gradient, unchanged residual; (7) transport of the packet PDE, divergence and quiet interval through the parabolic scaling at fixed viscosity, then through periodization, giving `zero_initial`; (8) `ClassicalSolutionT.sobolev`: a continuous `PeriodicSobolev m` datum path for every `m : ℕ`, plus `pressure_gradient`; (9) blow-up transport: map the packet witnesses near source time `1` into `t ↑ T` with spatial points inside `Q`; (10) exact energy change of variables, including `essSup`-vs-`IsLUB` for `M` and the endpoint-insensitive time interval, and the bridge from T13's `gradientENorm` to T10's `energyGradientT`; (11) mixed change of variables for all `1 ≤ p,q ≤ ∞` with both `∞` endpoints, producing the `MemLp` paths as well as the equality, and the `|Q| = 1` Haar-vs-Lebesgue identification; (12) time-integrated localization: apply `LocalizationAPI.localization` slice by slice with one `ε`-independent constant, combine Euclidean homogeneous scaling `ε^{-3/2-s}` with the `ε²` time change, and use `endpoint_zero`/`endpoint_one` at `s = 0,1`; (13) datum-path construction and strong measurability for `forceSobolev_memLp`; (14) negative-order monotonicity `forceSobolevENormT 1 s f ≤ forceSobolevENormT 1 0 f` for `s < 0` under the amended datum, then `forceConvergence` via the real-power limit through `ENNReal.ofReal` and `𝓝[>] 0`.

**Implementation candidates in `Paper1/`** (union of both COMPARISONs; none is imported, none discharges a T15 field on its own): `PeriodicScalingBounds.lean:19,40` `periodic_interpolation_of_endpoint_energies` / `periodic_interpolation_of_endpoint_bounds` (periodic `H⁰`–`H¹` interpolation once endpoints are supplied; explicitly not localization); `PeriodicPacketEndpointRates.lean:22,49,76,103` (scalar and vector whole-space endpoint rates at `s = 0,1`, inputs to the T13 transfer); `ScalingLimits.lean:11` `sobolev_error_tendsto_zero` (the real-power limit pattern — its exponents are the later **insertion** rates `ε^{1/2-s}+ε^{3/2-s}`, so T15 needs the simpler `ε^{1/2}+ε^{1/2-s}` companion, not a blind citation), `:27,29,35` `mixedExponent`/`mixedExponent_pos_iff`/`mixed_error_tendsto_zero` (exponent arithmetic), `energy_error_tendsto_zero` (T18, not T15). The single-copy lattice theorem, the T13-localization-to-`periodicSobolevENorm` bridge and the T10 datum-path witnesses have no local precedent.

## Open questions for the owner

1. The manuscript at `03-torus.tex:138`, both blind drafts, and the lead
   reconciliation prose specify only `q=1`, `s<1/2`.  The binding lane
   instruction instead explicitly requires `q : ℝ≥0∞`,
   `(q = 1 ∨ q = 2)`, and `s < criticalOrder q.toReal`.  `Spec.lean`
   follows the binding lane instruction.  Please confirm that the `q=2`
   strengthening is intended for T15 rather than only for registered I03/T18.
2. The reconciliation calls B's `R_*` a “derived convenience,” while also
   requiring A's 17 placement fields unchanged.  The spec therefore exports no
   primitive radius field; the implementation may derive one from compact
   `Kstar`.  Confirm no named derived definition is wanted in the eventual
   contract.
3. When T11/T13/T14 are registered, should the registration lane remove all
   three verbatim blocks at once, or retain the current namespace-qualified
   research snapshot for provenance while the contract imports only registered
   modules?

## U1 implementation status (lane 362)

The canonical bridge module is
`formalization/NSFormalization/Section3/T15/Bridges.lean`.  It imports T10's
periodic data and T13's periodizer, never `Contracts.*`, and defines the T15
rescalings over the canonical field types.  The three rescaling theorems are
`rfl` equalities to `Source.parabolicVelocity`, `Source.parabolicPressure`, and
`Source.parabolicForce`, which are the upstream objects named by the registered
bindings.  `alphaT_formula`, `normalizedScaledPressure_formula`,
`completedDense_eq_via`, `completedDenseHomogeneous_eq_via`, and
`periodize_eq_vendor` promote the remaining Spec drift checks.

`research/T15/probes/api_on_canonical.lean` copies the packet-specialized
definitions and proves each equals the canonical module by `rfl`; it also
proves the contract-side equalities for `scaledPacket`, `scaledPressure`,
`scaledForce`, and `alpha`.  The alpha bridge is necessarily formula-shaped in
the canonical module because the contract's `alpha` is a copied contract
definition with no separate upstream declaration.
