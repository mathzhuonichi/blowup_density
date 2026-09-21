# P6 Route B split

P6 / L21_H1 remains **Partial**. These are implementation units, not new
article-level closure claims.

| Unit | Owner | Status |
|---|---|---|
| B0 | lane 503 | Norm bridges / force cap; separate worktree, not imported here |
| B1 | lane 504 | Analytic steps closed and kernel-checked; registered-norm inequality conditional only on the exact B0 bridges below |
| B2 | unassigned here | Periodic estimate, including mean |
| B3 | lane 506 | Closed abstract real-analysis unit: uniform barrier, integrated dissipation and endpoint integrability |
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
