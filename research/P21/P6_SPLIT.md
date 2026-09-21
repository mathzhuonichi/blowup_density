# P21 / P6 Route B split

Status: **P6 remains Partial.**  The whole-space B5 theorem and registration are
closed in lane 510.  The periodic half and the final `L21_H1` closure remain for
lane 511.

| Unit | Exit condition | Size / model | Status |
|---|---|---|---|
| B0 | Reconcile H¹/H² Fourier norms with derivative energy and state shifted-force cap | M / sol | **Closed — lane 503.** Exact identities and finite caps on both domains; targets type-checked in `Targets.lean`. |
| B1 | General (no critical smallness) enstrophy interpolation/Young inequality on R³ | L / astra | Pending |
| B2 | Periodic version including mean and ordinary L² energy | L / astra | Pending |
| B3 | Uniform ODE barrier, integrated dissipation, endpoint monotone limit | M–L / astra | Pending |
| B4 | Maximal-lifespan contradiction, smooth common-interval restriction, regularity and pressure adapters | M / sol | **Closed on R³ — lane 507.** Exact `h1RestartR`, support-free bridges, and `h1RestartAt`; torus remains separate. |
| B5 | Uniform restartBeyond and registration/audits | M / sol | **Closed on R³ — lane 510.** Strict endpoint theorem and `A04.continuation_v3` registered; periodic endpoint and final `L21_H1` closure are lane 511. |

## B0 output

- `Section4/A04/H1Bridges.lean`: exact whole-space H¹/H² identities and the
  finite compact-window force cap.
- `Section3/T11/H1Bridges.lean`: exact periodic H¹/H² identities, the finite
  cap, and the smooth/periodic package for shifted forces.
- `Targets.lean`: `h1RestartR`, `h1RestartT`, `h1UniformEndpointR`, and
  `h1UniformEndpointT` as unproved `Prop` definitions in registered vocabulary.

## Remaining acceptance risks

- B1/B2 must prove the general cubic enstrophy inequality without importing
  the critical-smallness absorption from T20.
- B3 must choose the barrier time before restart time and datum, retain the
  inhomogeneous low modes, and justify endpoint integrability by monotone
  limits.
- B4 must argue through the already constructed smooth maximal solution; it
  must not infer a lower bound for the selected high-order local horizon.
- On the torus, B3/B4 may use B0's shifted smoothness, periodicity, and common
  `L²` cap, but not shifted membership in `forceClassT`.
- Lane 511 remains responsible for the periodic H¹ restart/endpoint theorems,
  their registered contract, and the graph/guide decision that closes
  `L21_H1`. Lane 510 has registered the whole-space half without changing that
  node's status.
# P6 Route B split

P6 / L21_H1 remains **Partial**. These are implementation units, not new
article-level closure claims.

| Unit | Owner | Status |
|---|---|---|
| B0 | lane 503 | Norm bridges / force cap; separate worktree, not imported here |
| B1 | lane 504 | Analytic steps closed and kernel-checked; registered-norm inequality conditional only on the exact B0 bridges below |
| B2 | unassigned here | Periodic estimate, including mean |
| B3 | lane 506 | Closed abstract real-analysis unit: uniform barrier, integrated dissipation and endpoint integrability |
| B4 | lane 507 | **Closed on R³.** Unconditional `h1RestartR` and `h1RestartAt`; no named analytic input |
| B5 | lanes 510/511 | **R³ closed and registered by lane 510.** Periodic endpoint, periodic registration, and final `L21_H1` closure remain lane 511. |

## B1 handoff

Module: `NSFormalization.Section4.A04.EnstrophyInequality`.
Main theorem: `enstrophy_differential_on_Icc`; pointwise version:
`enstrophy_differential`. For κ=(2π)⁻² and C₀=A05.gradientL6Const,

```
c = 1
Cν = (2κ C₀^(3/2))^4 / (κν/2)^3 / κ^3 + (1+ν) + (1+2κ/ν)
Y(t) = (D01.sobolevENorm 1 (slice w.velocity t)).toReal^2
Z(t) = (D01.sobolevENorm 2 (slice w.velocity t)).toReal^2
Y'(t) + ν Z(t) ≤ Cν (1+Y(t))^3 + Cν l2Sq(slice f t)
```

Exactly three norm hypotheses remain in this theorem, with z=velocity slice:

```lean
-- On all interior times (needed locally for differentiation):
(D01.sobolevENorm 1 z).toReal ^ 2 = l2Sq z + κ * gradientSq z
-- At each time in the chosen closed subinterval:
(D01.sobolevENorm 2 z).toReal ^ 2 ≤
  l2Sq z + 2 * κ * gradientSq z + κ ^ 2 * laplacianSq z
eLpNorm (A05.gradTensor z) 2 volume ≤ ENNReal.ofReal (Real.sqrt (gradientSq z))
```

These are ordinary norm-carrier bridges, not assumed nonlinear or differential
estimates. No B0 module was created. The parameterized theorem
`enstrophy_differential_of_norm_bridges` allows any fixed 0<κ≤1 if reconciliation
requires a different convention. The fixed κ matches the current Fourier weight
`(1+|ξ|²)^(s/2)` and the 2π derivative convention.

The independent `convection_sobolev` theorem consumes the two explicit bounds
`eLpNorm gradTensor 2 ≤ ofReal (2π * H1)` and
`eLpNorm lap 2 ≤ ofReal ((2π)^2 * H2)`, with Hm the finite real Sobolev norm.
Its underlying physical estimate `convection_interpolation` is unconditional.

No initial-time derivative or endpoint time integral is asserted. Compact
intervals lie strictly inside (0,T). B3 must still perform the uniform barrier
and endpoint limit; strict-interior finiteness alone does not suffice.

## B3 handoff

Module: `NSFormalization.Section4.A04.EnstrophyBarrier` (independent of B0/B1).
`enstrophy_uniform_barrier_and_dissipation` chooses d>0 and M before all restart
times, interval lengths and functions. The proof chooses
`d = 1 / (4*C*(1+F)*(1+K)^2)` and `M = 2*(1+K)-1`.
For `0 ≤ S ≤ d`, a continuous nonnegative Y, differentiable only on the open
interval, initial value at most K, nonnegative Z, and
`deriv Y t + c*Z t ≤ C*(1+Y t)^3 + C*F`, it gives the closed-interval
bound Y≤M and `∫ Z ≤ (K+C*(1+M)^3*S+C*F*S)/c`.
Z integrable on the compact interval is an explicit hypothesis for this
integrated result. No integrability of `deriv Y` is required.

`enstrophy_endpoint_lintegral` passes any uniform nonnegative-integral bound
on `Ico a s`, s<b, to `Ico a b` (even without measurability).
`enstrophy_endpoint_integral` takes measurable nonnegative Z, local compact
integrability, and real interval-integral bounds for a≤s<b; it returns BOTH
`IntegrableOn Z (Icc a b)` and the endpoint real integral bound. The local
integrability premise is essential for Lean's totalized real integral; it is
supplied by the compact-interval B3 estimate in B4 applications. Singleton
endpoints have zero Lebesgue measure. No endpoint derivative is assumed.

All six exported theorems have exactly the standard three logical axioms.
B3 does not import, reimplement or modify the B0 norm bridges. B4 still must
supply time continuity, interior differentiability, force bounds and local
integrability from classical solutions, then apply the existing H² continuation
criterion and maximality. P6 / L21_H1 remains Partial.


## B4 handoff — lane 507 (R³)

**Whole-space B4 is closed; P6's registered status remains Partial pending the
separate torus work and final lane-511 closure.**
`Section4/A04/H1Restart.lean:h1RestartR` proves
exactly the local-name version of `Targets.lean:h1RestartR`, with one δ before
restart time and smooth admissible datum, and all manuscript regularity on that
same interval. The research probe proves the literal target Prop using existing
contract structure conversions. No contract or blueprint status is changed.

### Corrections to the earlier B0/B1 interface discussion

- The registered whole-space datum uses **angular**, not cycles, frequency.
  `Source.angular_partial_norm_sq` cancels `2π`. Thus **κ=1** is the correct
  parameter for B1's `enstrophy_differential_of_norm_bridges`. The preceding
  historical B1 handoff's κ=(2π)⁻² is not used by B4.
- `forceL2CapR` bounds the L² norm. B3's real force-energy parameter is
  **`(forceL2CapR f S).toReal ^ 2`**.
- `H1BridgesSmooth.lean` proves the support-free exact successor/H¹/H² identities
  via D01's sharp raising identity and smooth weak derivatives, and proves the
  Frobenius-gradient norm identity. Compact support and a new approximation
  theorem are unnecessary. All reviewed modules remain untouched.

### Consumer API for B5

`h1RestartAt ν hν f hf S hS K hK` returns one `δ>0` and

```lean
∀ (a : SpatialField) (u : SpaceTimeField) (p : SpaceTimeScalar),
  SolvesBelow ν a f S u p → ∀ t₀ ∈ Ico (0 : ℝ) S,
    sobolevENorm 1 (C01.slice u t₀) ≤ K →
      ENNReal.ofReal (t₀ + δ) ≤ maximalLifespanR ν a f
```

It uses `w.restart_datum` and the proved `shiftedLocalExtension`, with no
hypothesis naming a local supplier or extension principle. B5 can feed the
per-time conclusion into `restartBeyond_of_restartAt`, obtaining
`ofReal (S+δ) ≤ maximalLifespanR`. For the strict endpoint target return δ/2;
`ofReal (S+δ/2) < ofReal (S+δ)` follows from S>0 and δ>0. This is an existential
horizon theorem, not a lower bound on `A01.localHorizon'`.

For contract transport, the copied scalar/field/norm definitions are `rfl`;
`ClassicalSolutionR` itself is a distinct structure. Use
`Bindings.maximalPartial_ofA02` and
`Bindings.localTheoryV2_regularity_ofA02`, as kernel-checked in
`probes/b4_closes.lean:registered_target`.

The endpoint proof uses B3's **lintegral** theorem and explicit finiteness-based
conversion of the registered squared norm. This proves a bound on
`squaredHTwoIntegral` directly and avoids a global measurability claim outside
the solution's constrained interval. Arbitrary classical regularity is supplied
by `classical_hasSmoothSobolevPath` (uniqueness on overlapping carrier windows)
and A01's general pressure recovery, projected equation and gauge theorems.

## B5 R³ handoff — lane 510

The whole-space B5 unit is closed. The new
`Section4/A04/H1RestartBeyond.lean` exports:

- `RestartFixedForceH1 ν f S`, the named body of the fixed-force H¹ restart;
- `restartBeyondH1_le`, which applies `restartBeyond_of_restartAt` to lane
  507's `h1RestartAt` and retains the full non-strict endpoint margin;
- `restartBeyondH1`, the exact strict `h1UniformEndpointR` shape, obtained by
  returning half that margin.

`Contracts/V3/Continuation.lean` adds exactly the registered-vocabulary
`restartH1` and `restartBeyondH1` fields. `Bindings/ContinuationV3.lean`
transports the distinct classical-solution records with the existing V2
fieldwise conversions, and `Tests/ContinuationV3.lean` registers
`BlowupDensity.Tests.checkedContinuationV3`. The registry now has 35 enabled
contracts. `A04.continuation_v2` is unchanged and remains separately
registered for the H⁷/integral routes.

Lane 511 still needs all of the following before changing `L21_H1` from
`Partial`:

1. Prove the registered-vocabulary periodic `h1RestartT` and
   `h1UniformEndpointT` targets. The latter must return a solution on
   `S + δ` with literal velocity and normalized-pressure agreement on
   `[0,S)`. `Section3/T11/RestartBeyond.lean:restartBeyond` contains the
   gluing argument, but its public theorem is conditional on
   `PeriodicQuantitativeLocalInput'`; the final theorem must consume the proved
   unconditional H¹ restart rather than register that named input.
2. Register both periodic H¹ fields in a new versioned contract/binding/test,
   preserving the frozen V1/H³ and V2 registrations and the whole-space
   `A04.continuation_v3` registration.
3. Add periodic non-vacuity and exact-axiom probes, then update the authoritative
   `L21_H1` scope/evidence, result map, guide, generated dependency graph and
   axiom audit. Only after both domains are registered should the node become
   `Closed`.

Lane 510 deliberately leaves `formalization/blueprint/proof_graph.json`, the
guide coverage row and the `L21_H1` status unchanged.
