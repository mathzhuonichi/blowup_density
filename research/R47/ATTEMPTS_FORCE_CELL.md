# Lane 251 — force cell integral

## Implemented route

- Read `CLAUDE.md`, HANDOFF §0, LESSONS first 40 lines, NEXT_SESSION/PLAN,
  REPORT_247 §3, RECONCILIATION, Spec, the R42 contract and Assembly,
  and `04-whole-space.tex:297-330`.
- The paper's actual display is a time derivative of the velocity mean plus
  the surface flux of `uε ⊗ uε − v ⊗ v + (pε−π)I − ν∇(uε−v)`.
  It does **not** assert that the force difference is divergence free.
- `Paper3.setIntegral_component_eq_zero` proves the velocity component result.
  The support is compact: closed topological support lies in the closed ball.
  `ComparatorBridge.divergence_eq` translates R42's coordinate divergence.
  Spatial slicing of `ContDiffOn` works at zero without ambient time smoothness.
- Commuting the Euclidean projection with the integrable vector integral gives
  the exact vector premise of lane 247's `gridObservation_locality`.
- The search of Paper3/Source and Section4/D01,A03,A04,A01,C01 found
  `Paper3.TimeObservations.integral_timeDerivative_component_eq_zero` and
  `Paper3.ForceObservations.integral_spatialPartial_eq_zero`, as well as
  `A04/AdvectionDivergence` and the existing slab assembly. The time lemma is
  applied on `[t/2,(t+T)/2]`, dominated by the fixed closed insertion ball.
  Thus differentiation under the integral and zero temporal mean are proved,
  not included in the remaining input.
- `insertion_momentum_difference` uses `A.momentum`, `A.reference.momentum`,
  `reference_velocity`, `reference_pressure`, and positive reference margin.
  It subtracts residuals; it never treats the nonlinear residual as linear.
- At zero, `forceDifference_compact` has positive-time support and forces
  pointwise equality. Neither momentum at zero nor a two-sided derivative is
  assumed. The standalone initial observation theorem needs no containing cell.
- Continuous fields are integrable on cells: put each half-open cell inside
  the compact image under `WithLp.toLp` of its closed coordinate box.
  Force observations use `hg : MemForceR A.g`, the regular-reference force
  assumption from R47. This assumption is absent from the bare R42 record.

## One remaining analytic input, exact statement

For the fixed actual record `A`, `hcompactMomentumIntegral` is:

```
∀ ε ∈ Ioc 0 A.ε₀, ∀ (grid : Grid) (k₀ : Fin 3 → ℤ),
  A.ball ⊆ grid.cell k₀ → ∀ t ∈ Ioo 0 A.T,
  (∫ x in grid.cell k₀,
    (navierStokesResidual ν (A.velocity ε) (A.pressure ε) t x -
     navierStokesResidual ν A.v A.π t x)) =
  (∫ x : Space, deriv (fun s => A.velocity ε (s,x) - A.v (s,x)) t)
```

Here both residuals are `NavierStokesR3.ProblemStatement.navierStokesResidual`.
This is spatial flux cancellation and restriction-to-whole-space for the
supported temporal term. It mentions neither the force nor observations.
It is an explicit theorem argument, not an added record field or an axiom.
It is **not proved in this lane**.

### Satisfiability for the actual inserted family

Set `w=uε−v`, `q=pε−π`. At each interior time, the flux component is

`Q[j,i] = uε_j*uε_i − v_j*v_i + (if i=j then q else 0) − ν*∂ᵢw_j`.

The two velocities are smooth and divergence free. Product differentiation
therefore expresses the residual difference as `∂ₜw_j + Σᵢ ∂ᵢ Q[j,i]`.
Outside the closed support of `w` and `q`, the fields agree on a neighborhood,
so the flux vanishes there. These supports are compact and contained in the
open insertion ball, hence in the interior of any cell containing that ball.
The spatial derivatives have the same support property. Their integrals are
zero by the existing compact-partial lemma. Uniform containment of `w` in the
fixed ball on an interior time window also puts its time derivative in the
closed ball; outside the containing cell the time trace is identically zero
on that window. Thus its cell and whole-space integrals coincide.

This argument applies to the nonstationary, nonzero R42 insertion. It requires
no global-in-time smoothness across the blowup time, no behavior at negative
times, and no false zero-time ambient derivative assumption. A Lean proof of
the flux expansion/support/integral assembly remains the follow-up task; the
non-vacuity probes do not claim to provide a Lean witness of this open input.

## Failed or revised approaches

- A first conditional version left both temporal differentiation and flux
  cancellation in a residual/derivative-of-cell-mean identity. Replaced it
  after finding the existing compact time-integral theorem; only the spatial
  identity above remains.
- `Space` was ambiguous after opening both contract and upstream namespaces;
  keep only the contract opening. Smoothness notation requires `ContDiff` scope.
- Rewriting syntactically different but definitionally equal residual aliases
  failed; explicitly type the inserted equation and use congruence on the
  reference equation.
- `Space` has no `Preorder`, so `isCompact_Icc` cannot directly describe its
  boxes. Use a product of real closed intervals and `WithLp.toLp` instead.
- Time-window `linarith` needs the explicit projections `ht.1`, `ht.2`.
  The support-zero lemma also needs an explicit slice function; inference
  otherwise selects the joint field or the subtraction function.

## Scope

Only new files. No registration, full `RGridFamily` construction, or convergence
claim. Velocity conclusions are unconditional; force conclusions are conditional
on exactly the displayed spatial identity (except at zero, unconditional).
