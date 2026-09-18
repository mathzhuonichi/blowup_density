# T15 draft A comparison — `prop:scaling`

This is the blind-A statement comparison for
`paper/sections/03-torus.tex:101-159`. It does not use any other T15 draft or
brief. The Section 4 comparison target is the registered contract
`I03.scaling`, `verification/Contracts/V1/Scaling.lean`.

## 1. Paper clause to Lean field

| Paper clause | Draft-A declaration / field | `I03.scaling` counterpart | Notes |
|---|---|---|---|
| Choose compact `K_*` containing `K` and the spatial projection of `supp F` (`:101-102`) | `PlacementData.Kstar`, `Kstar_compact`, `carrier_subset`, `force_projection_subset` | `ScalingAPI.carrier_subset` only covers the packet carrier | T15 retains the force-support enlargement that the registered I03 docstring says is missing there. |
| Fixed coordinate ball and `x₀∈B` (`:102-105`) | `chartCenter`, `chartRadius`, `chartRadius_pos`, `chartBall_in_cube`, `x₀`, `x₀_mem` | I03 obtains `x₀,r` from `CorrectionAPI`; no torus chart | The closed ball lies in the interior of T13's fixed fundamental cube. |
| `2ε²<T`, `x₀+εK_*⊂B`, `t_ε=T-ε²` (`:103-107`) | `ε₀`, `eps_pos`, `eps_le_one`, `eps_time`, `eps_space`; `packetTimeShift` | `ε₀`, `eps_pos`, `eps_le_one`, `eps_time`, `eps_space` | T15 uses the exact torus placement inclusion; I03 uses a radius inequality for the correction geometry. |
| Negative-time zero extensions (`:108-111`) | `scaledVelocity`, `scaledPressure` use `zeroPastField`; `scaledForce` uses the already zero-extended packet force | `scaledPacket`, `scaledPressure`, `scaledForce` | Same convention and time-first `SpaceTime` ordering. |
| Three formulas of `eq:scaling` (`:112-118`) | `scaledSourcePoint`, `scaledVelocity`, `scaledPressure`, `scaledForce` | `scaledPacket`, `scaledPressure`, `scaledForce` | Amplitudes are `ε⁻¹`, `ε⁻²`, `ε⁻³`; time and space scales are `ε⁻²`, `ε⁻¹`. |
| Place in `B`, periodize, single copy (`:120`) | `periodizeVelocity`, `periodizePressure`, the three `periodizedScaled*` defs; `velocity_single_copy`, `pressure_single_copy`, `force_single_copy` | None: I03 is explicitly whole-space | The rendering is the lattice sum over `ℤ³`; `eps_space` plus `chartBall_in_cube` is the single-copy hypothesis. |
| Solve periodic momentum equation at the same viscosity (`:122-123,141`) | `velocity_smooth`, `pressure_smooth`, `force_mem`, `velocity_periodic`, `pressure_periodic`, `divergence`, `momentum` | `scaledEquation`, `scaledDivergenceFree` | Draft A uses a pointwise PDE for the fixed explicit fields. This prevents an existential `ClassicalSolutionT` witness from substituting different velocity or pressure fields. |
| Start from zero (`:123`) | `zero_initial` | No separate I03 field; derived there from the negative-time extension and `eps_time` | Kept explicit because it is a proposition clause and T18 consumes a zero packet history. |
| Unbounded speed at `T` (`:123,142-143`) | `speed_unbounded` using registered `SpeedUnboundedAt` | `scaledBlowup` | Exact quantifiers: for every `M>0` and `δ>0`, there exist `t∈(0,T)`, `x`, with `T-δ<t` and `M<‖u(t,x)‖`. |
| Spatially constant pressure adjustment and mean-zero gauge (`:123`) | `normalizedScaledPressure`; `pressure_adjustment_constant`, `pressure_gauge` | None | The raw pressure has the single-copy identity; the normalized pressure differs from it by a time-dependent spatial constant and is used in `momentum`. |
| `‖U_ε‖_{L∞L²}=ε^{1/2}M` (`:125-126`) | `energy_finite`, `packetEnergyIdentity` with T10 `energyEssSupT` | `packetEnergyIdentity` with Section 4 `Data.energyEssSup` | Both are equalities in `ℝ≥0∞`, with `M=P.energyBound`. |
| `‖∇U_ε‖_{L²L²}=ε^{1/2}D` (`:127-128`) | `energy_finite`, `packetDissipationIdentity` with T10 `energyGradientT` | `packetDissipationIdentity` with `Data.energyGradient` | Both are equalities in `ℝ≥0∞`, with `D=P.dissipationBound`. |
| `α(p,q)=-3+3/p+2/q` (`:129-132`) | `alphaT` | `Correction.alpha` | Both use `ENNReal.toReal`; at `p=∞` or `q=∞`, division by `0` yields the intended zero reciprocal. |
| Mixed-norm identity for `1≤p,q≤∞` (`:129-133,148-149`) | `mixed_mem`, `packetMixedScaling`; torus `mixedLebesgueENormT` on the left and registered whole-space `mixedLebesgueENorm` on the right | `packetMixedScaling` | `mixed_mem` adds explicit `MemLp` representatives, including the essential-supremum endpoints. |
| `C_s` is fixed before `ε` (`:133-136`) | data field `sobolevConst : ℝ → ℝ`, then `sobolevConst_pos` | `positiveConst` | The Type-valued API style matches A03/A05: the constant is structure data, not an `∃ C` nested after `ε`. It may depend on the already-fixed packet and chart, but not on scale. |
| `‖F_ε‖_{L¹H^s(T³)}≤C_s(ε^{1/2}+ε^{1/2-s})`, `0≤s≤1` (`:133-136,150-158`) | `sobolev_mem`, `packetSobolevBound`, with the parameter `localizationAPI` and its field `LocalizationAPI.localization` | Closest field: `packetPositiveScaling` | I03 is whole-space and gives the general positive-order Section 4 rates. T15's torus bound specifically depends on T13 localization. |
| “In particular” convergence for every `s<1/2`, including negative `s` (`:138,158`) | separate predicate `ForceConvergesBelowCritical` | Closest field: `forceConvergence` | It is deliberately not a `ScalingAPI` assumption. Future code should derive it from `packetSobolevBound` for `0≤s<1/2`, and from periodic `H^s≤L²` monotonicity for `s<0`. |

## 2. Representation choices

### Periodization

Draft A uses

```text
periodize f (t,x) = Σ' n : ℤ³, f(t,x-n).
```

This agrees with T13's spatial `periodize` and makes periodicity algebraic. It
also exposes the proof obligation that the infinite sum is locally finite.
The explicit-cube-representative alternative was rejected for the PDE fields:
it would make differentiability across the cube boundary an additional
definition-level problem.

The raw velocity, raw pressure, and force equal their zero-lattice copy on the
fixed fundamental cube. The hypotheses responsible are, in order:

1. `Kstar` covers the velocity/pressure carrier and the spatial force support;
2. `eps_space` places `x₀+εKstar` inside the chart ball;
3. `chartBall_in_cube` separates that support from all nonzero lattice
   translates.

The normalized pressure does not literally equal its raw single copy: it is
that copy minus a spatial constant. This is why Draft A states
`pressure_single_copy` for the raw periodization and separately states
`pressure_adjustment_constant` and `pressure_gauge` for the PDE pressure.

### Scale range

Every conclusion uses one interval `ε ∈ Set.Ioc 0 ε₀`. The placement record
requires `0<ε₀≤1`, `2ε²<T`, and `x₀+εK_*⊂B` throughout that interval. The
upper normalization `ε₀≤1` is harmless after shrinking and is useful for
endpoint/interpolation estimates. `2ε²<T`, rather than only `ε²<T`, follows
the paper literally and ensures `t_ε>0` with room to spare.

### Norm codomains and integrability

The following are `ℝ≥0∞`-valued:

- `energyEssSupT` and `energyGradientT`;
- `mixedLebesgueENormT` and Section 4's `mixedLebesgueENorm`;
- `forceSobolevENormT` and the spatial periodic Sobolev norm.

The scale `ε`, constants `M,D,C_s`, and the exponent `alphaT` are real. Real
powers are converted by `ENNReal.ofReal` exactly as in I03. `energy_finite`,
`mixed_mem`, and `sobolev_mem` prevent totalized norms or empty path infima
from concealing failed integrability. In addition, `force_mem` records that
the periodized force is smooth and compactly supported in positive time.

### PDE shape

Draft A states the pointwise periodic PDE, divergence, regularity,
periodicity, initial condition, and gauge separately. This is
`ClassicalSolutionT`-shaped but is not bundled as an existential solution.
The reason is anti-substitution: all conclusions visibly mention the exact
periodized-and-normalized definitions. A later binding can package these
fields into `ClassicalSolutionT` once its Sobolev trajectory field has been
constructed.

## 3. Ambiguities and decisions

- The displays write `U_ε(x,t)`, while every repository `SpaceTime` uses
  `(t,x)`. Draft A follows the repository convention and records the paper
  order only in docstrings.
- The paper calls `B` “the ball in Lemma localization” without fixing a
  fundamental cube. Draft A uses T13's fixed `[0,1]³` cube and requires the
  closure of `B` to lie in its interior.
- The paper says the torus contains a single copy, but does not choose between
  a lattice sum and a quotient representative. Draft A chooses the lattice
  sum and states the agreement on the cube explicitly.
- `K_*` is not a radius in the paper. Draft A keeps the exact compact-set
  inclusion `x₀+εK_*⊂B`, rather than replacing it by a stronger ball-radius
  estimate.
- The paper does not spell out whether `C_s` can depend on the packet and
  chart. Draft A lets it depend on all data fixed before `ε`, which is the
  uniformity actually used.
- T13's reconciled source namespace is `BlowupDensity.T13.Spec`, while the
  lane brief requires copied declarations under `BlowupDensity.T13.Draft`.
  Draft A follows the lane brief; the copied declaration bodies and names are
  otherwise unchanged.
- The exact mixed identity is between a periodic spatial norm on the left and
  a whole-space spatial norm on the source packet on the right. Reusing
  Section 4's whole-space norm for the periodic lift would give `∞` for every
  nonzero periodic field, so Draft A defines the torus analogue instead.
- The proposition's negative-order convergence is not a direct instance of
  `eq:packetHs`, whose stated range is `0≤s≤1`. Draft A therefore makes it a
  separate derived predicate and records the missing monotonicity lemma.

## 4. Needs a lemma

1. **Scaled support placement.** From `PacketAPI.velocity_support`,
   `pressure_support`, `force_projection_subset`, and `eps_space`, prove that
   each relevant scaled slice is supported in the fixed chart ball.
2. **Single-copy/local-finiteness.** Prove the lattice `tsum` is locally
   finite, is unit-periodic, and equals the zero-lattice summand on the
   fundamental cube. Separate vector and scalar versions are needed.
3. **Smooth periodization.** Commute finite local periodization with all
   derivatives used by `navierStokesResidual`, including the nonlinear term.
4. **Pressure normalization.** Prove `normalizePressureT` is periodic and
   smooth, has zero torus mean, differs by a spatial constant, and has the
   same spatial gradient as the raw pressure.
5. **Initial and PDE transport.** Transfer T14's smooth zero-extension PDE,
   divergence, and quiet interval through the exact parabolic scaling at fixed
   viscosity and then through periodization.
6. **Blow-up transport.** Map the packet witnesses near source time `1` into
   times near `T`, place their spatial points in the fundamental cube, and use
   the single-copy equality.
7. **Energy change of variables.** Prove both exact T10 energy identities,
   including the essential supremum and endpoint-insensitive time interval.
8. **Mixed change of variables.** Construct the whole-space and torus `Lp`
   paths, prove `MemLp`, and establish the exact formula for finite exponents
   and both `∞` endpoints.
9. **Time-integrated localization.** Apply
   `LocalizationAPI.localization` slice-by-slice with one constant independent
   of `ε`, combine Euclidean homogeneous scaling with the `ε²` time change,
   and treat `s=0,1` using `endpoint_zero` and `endpoint_one`.
10. **Periodic norm bookkeeping.** Bridge T13's cube-restricted physical
    endpoint equalities to T10's Haar/Fourier norm and prove the measurable
    Sobolev path required by `sobolev_mem`.
11. **Subcritical convergence.** Use real-power convergence for
    `0≤s<1/2`; for `s<0`, prove `periodicSobolevENorm s z ≤
    periodicSobolevENorm 0 z` and combine it with the `s=0` bound.
12. **Registration bridges.** Once T10/T13/T14 are registered, add `rfl`
    bridges for every copied definition and replace the temporary copies.

## 5. `Paper1/` implementation candidates (not imported)

- `PeriodicScalingBounds.lean:19`
  `periodic_interpolation_of_endpoint_energies` and `:40`
  `periodic_interpolation_of_endpoint_bounds` provide the periodic `H⁰`–`H¹`
  interpolation step once endpoint identities/bounds are supplied. They do
  not prove localization.
- `ScalingLimits.lean:11` `sobolev_error_tendsto_zero` supplies the real-power
  limit pattern; `:27` `mixedExponent`, `:29`
  `mixedExponent_pos_iff`, and `:35` `mixed_error_tendsto_zero` supply exponent
  arithmetic. The exact two terms there belong to its existing insertion
  estimate, so T15 must instantiate/check the paper's
  `ε^{1/2}+ε^{1/2-s}` bound rather than cite it blindly.
- `PeriodicPacketEndpointRates.lean:22,49,76,103` proves scalar/vector
  whole-space packet endpoint rates at `s=0,1`. These are useful inputs to the
  T13 transfer but are not themselves periodic localization or exact torus
  identities.
