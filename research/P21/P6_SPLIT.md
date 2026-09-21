# P6 Route B split

P6 / L21_H1 remains **Partial**. These are implementation units, not new
article-level closure claims.

| Unit | Owner | Status |
|---|---|---|
| B0 | lane 503 | Norm bridges / force cap; separate worktree, not imported here |
| B1 | lane 504 | Analytic steps closed and kernel-checked; registered-norm inequality conditional only on the exact B0 bridges below |
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
