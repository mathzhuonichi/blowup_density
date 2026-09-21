# P6 Route B split

P6 / L21_H1 remains **Partial**. These are implementation units, not new
article-level closure claims.

| Unit | Owner | Status |
|---|---|---|
| B0 | lane 503 | Norm bridges / force cap; separate worktree, not imported here |
| B1 | lane 504 | Analytic steps closed and kernel-checked; registered-norm inequality conditional only on the exact B0 bridges below |
| B2 | lane 505 | Partial: full H¹ Fourier derivative, Haar Hölder/interpolation, gradient L⁶ for arbitrary mean, localized velocity L⁶, and scalar Young assembly closed; velocity embedding and physical pairing assembly remain |
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

## B2 handoff (partial)

Module: `NSFormalization.Section3.T11.EnstrophyInequality`. Ten declarations
are proved; see `REPORT_505.md` and `ATTEMPTS_B2.md` for exact residuals.
There is **no** `enstrophy_differentialT` or
`enstrophy_differential_on_IccT` yet. B3/B4 cannot consume this as a proved
classical periodic differential inequality.

`inhomogeneousEnergyIdentityT` differentiates the registered full H¹ norm,
including the mean, but its RHS still uses Fourier H¹ pairings.
`convection_interpolationT` still has the velocity L⁶ factor.
`weighted_cubic_assemblyT` is scalar algebra: Y=U+G,
Z≤U+2G+L, |N|≤C Y^(3/4) L^(3/4) give

```
d + ν Z ≤ ((2C)^4/(ν/2)^3 + (1+ν)) (1+Y)^3 + (1+2/ν) F.
```

The periodic Fourier weight is 1+|2πk|², so κ=1, **not** the R³ κ in
the B1 handoff. The corresponding three B0 interfaces, with z a velocity
slice and namespaces T10/T12/T20 open, are:

```lean
(periodicSobolevENorm 1 z).toReal ^ 2 = lTwoSqT z + gradientSqT z
(periodicSobolevENorm 2 z).toReal ^ 2 ≤
  lTwoSqT z + 2 * gradientSqT z + laplacianSqT z
eLpNorm (torusLift (gradientTensor z)) 2 periodicTorusMeasure ≤
  ENNReal.ofReal (Real.sqrt (gradientSqT z))
```

As in B1, the first is needed on all interior times for a physical derivative
transfer; the other two are pointwise on the compact interval. These are
the intended normalized torus counterparts, not new B0 theorems. None is
assumed by the ten delivered declarations; no final consumer has yet been
proved in which to thread them. No B0 module was created or imported.

The exact remaining localized velocity estimate is
```lean
eLpNorm (gradientTensor (cutoffMul z)) 2 volume ≤
  343 * (3 * (ENNReal.ofReal cutoffGradBound * periodicLpENorm 2 z +
    periodicLpENorm 2 (gradientTensor z)))
```
for `SmoothPeriodicT z`. Together with the delivered localization theorem
this gives a mean-retaining velocity L⁶ bound. The other residual is the
physical RHS conversion of the full H¹ identity, spelled out in
`ATTEMPTS_B2.md`. These are B2 analytic residuals, not B0 norm obligations.
