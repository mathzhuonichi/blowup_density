# P6 Route B split

P6 / L21_H1 remains **Partial**. These are implementation units, not new
article-level closure claims.

| Unit | Owner | Status |
|---|---|---|
| B0 | lane 503 | Norm bridges / force cap; separate worktree, not imported here |
| B1 | lane 504 | Analytic steps closed and kernel-checked; registered-norm inequality conditional only on the exact B0 bridges below |
| B2 | unassigned here | Periodic estimate, including mean |
| B3 | lane 506 | Closed abstract real-analysis unit: uniform barrier, integrated dissipation and endpoint integrability |
| B2 | lane 505 | Closed conditional only on the three torus norm bridges below; both analytic residuals and final differential inequality kernel-checked |
| B3 | unassigned here | ODE barrier, integrated dissipation, endpoint monotone limit |
| B4 | unassigned here | Maximal-lifespan contradiction and common smooth interval |
| B5 | unassigned here | Uniform restart and final registration |

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
# P21 / P6 Route B split

Status: **P6 remains Partial.**  This file tracks the preferred smooth-data,
fixed-force Route B from `ASSESSMENT.md` §3.  Closing B0 supplies norm and force
bridges; it does not prove H¹-uniform restart or either endpoint target.

| Unit | Exit condition | Size / model | Status |
|---|---|---|---|
| B0 | Reconcile H¹/H² Fourier norms with derivative energy and state shifted-force cap | M / sol | **Closed — lane 503.** Exact identities and finite caps on both domains; targets type-checked in `Targets.lean`. |
| B1 | General (no critical smallness) enstrophy interpolation/Young inequality on R³ | L / astra | Pending |
| B2 | Periodic version including mean and ordinary L² energy | L / astra | Pending |
| B3 | Uniform ODE barrier, integrated dissipation, endpoint monotone limit | M–L / astra | Pending |
| B4 | Maximal-lifespan contradiction, smooth common-interval restriction, regularity and pressure adapters | M / sol | Pending |
| B5 | Uniform restartBeyond and registration/audits | M / sol | Pending |

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
- B5 remains responsible for the actual H¹ restart/endpoint theorems and any
  ensuing contract, binding, test, graph, guide, or registry decision.

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

## B2 handoff (closed conditional on three bridges)

Module: `NSFormalization.Section3.T11.EnstrophyInequality`.
Main theorem: `enstrophy_differential_on_IccT`; pointwise theorem:
`enstrophy_differentialT`; separate-coefficient companion:
`enstrophy_differential_of_norm_bridgesT`. Both residuals A/B are closed; see
`ATTEMPTS_B2.md` and the cont section of `REPORT_505.md`.

```
Cv = velocitySixConstT = 3*343*A05.gradientL6Const*(1+cutoffGradBound)
C = convectionConstT = √2 * Cv * √Csix
c = κ = 1
Cν = (2*C)^4/(ν/2)^3 + (1+ν) + (1+2/ν)
Y(t) = (periodicSobolevENorm 1 (slice w.velocity t)).toReal^2
Z(t) = (periodicSobolevENorm 2 (slice w.velocity t)).toReal^2
Y'(t) + ν Z(t) ≤ Cν (1+Y(t))^3 + Cν lTwoSqT(slice f t)
```

The force is `f ∈ T10.forceClassT`, definitionally `T10.MemForceT f`.
The solution is canonical `T10.ClassicalSolutionT ν a f T`, with arbitrary
initial datum and retained mean. No critical smallness is used.
The three hypotheses, with z the appropriate velocity slice, are exactly:

```lean
-- hOne: all times in Ioo 0 T
(periodicSobolevENorm 1 z).toReal ^ 2 = lTwoSqT z + gradientSqT z
-- hTwo: each time in Icc r s
(periodicSobolevENorm 2 z).toReal ^ 2 ≤
  lTwoSqT z + 2 * gradientSqT z + laplacianSqT z
-- hGradient: each time in Icc r s
periodicLpENorm 2 (gradientTensor z) ≤
  ENNReal.ofReal (Real.sqrt (gradientSqT z))
```

The last left side is definitionally
`eLpNorm (T10.torusLift (gradientTensor z)) 2 periodicTorusMeasure`.
The energies are the existing T20 `lTwoSqT/gradientSqT/laplacianSqT`, each
squared `toReal` of the corresponding periodic L² norm. The theorem assumes
`0 < r`, `s < T`, and concludes at every `t ∈ Icc r s`, matching B1.
No initial-time or maximal-endpoint assertion is made.

### Exact B4 reconciliation obligations with lane 503

Lane 503's `H1Bridges.lean` is not imported or restated. For smooth periodic z,
B4 needs these equalities between its physical component-integral energies
and the T20 energies used here:

```lean
periodicL2Energy z = T20.lTwoSqT z
periodicGradientEnergy z = T20.gradientSqT z
periodicHessianEnergy z = T20.laplacianSqT z
```

The first two are Haar/cube and finite-component L² norm conversions.
The third is the periodic Parseval identity equating the sum of all ordered
second-partial energies with the Laplacian energy; it is **an outstanding
B4 reconciliation obligation**, not definitional equality and not proved here.
After those conversions, rewriting lane 503's
`periodicSobolevENorm_one_toReal_sq_eq` yields hOne; rewriting its
`periodicSobolevENorm_two_toReal_sq_eq` and taking `.le` yields hTwo.
For hGradient, prove the gradient L² norm finite from continuity on the torus,
then rewrite `gradientSqT`, `Real.sqrt_sq ENNReal.toReal_nonneg` and
`ENNReal.ofReal_toReal`; this is an ordinary norm conversion.

There are no remaining B2 nonlinear/differential hypotheses. B3 still owes
the ODE barrier and endpoint integration; B4/B5 still owe their respective
lifespan/restart assemblies. P6 / L21_H1 remains Partial.
