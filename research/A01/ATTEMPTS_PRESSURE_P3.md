# Lane 168 — A01 constructor pressure P3

## Outcome

`Section4/A01/ConstructorPressure.lean` now constructs, from a force and a
candidate velocity, the basepoint-gauged pressure

```lean
pressureOfVelocity ν f velocity =
  pressurePotential (pressureGradientOfVelocity ν f velocity)
```

where

```lean
momentumResidualOfVelocity ν f velocity
  = f - (velocity · ∇)velocity + ν Δvelocity

pressureGradientOfVelocity ν f velocity
  = momentumResidualOfVelocity ν f velocity - ∂ₜvelocity.
```

Thus the physical vector field is explicit; no arbitrary representative is
selected from a Fourier datum.  The scalar potential is the already-proved
radial construction in `A01/RadialPotential.lean`, and
`pressureOfVelocity_basepoint` fixes its gauge by `p(t,0) = 0`.

## Successful route

1. `pressureGradient_pressureOfVelocity` applies
   `RadialPotential.pressureGradient_pressurePotential` to a spatially smooth,
   symmetric-Jacobian slice.  It gives the pointwise equality
   `∇p(t,x) = pressureGradientOfVelocity ν f velocity (t,x)`.
2. `pressureGradient_pressureOfVelocity_lerayComplement` assumes the
   datum-form projected equation

   ```lean
   orderZeroDatum htime =
     orderZeroDatum hres -
       D01.Leray.lerayComplement 0 (orderZeroDatum hres)
   ```

   where `hres` and `htime` are the `MemLp` proofs for the residual and
   `∂ₜvelocity`.  `D01.orderZeroDatum_sub` then computes the datum of
   `residual - ∂ₜvelocity`, and abelian-group cancellation leaves exactly
   `(I-P) datum(residual)`.  This is the constructor-side analogue of
   `D01.isSobolevDatum_pressureGradient_lerayComplement`, without taking an
   already-built `ClassicalSolutionR` as input.
   `pressureGradient_pressureOfVelocity_lerayComplement_order` then uses
   `Leray.isSobolevDatum_lower_iff` and
   `Leray.lerayComplement_lowerVectorL` to promote the pin to every integer
   order carried by the residual.
3. `pressure_gradient_memLp` proves the complete c9 row on `Ico 0 T` from the
   corresponding slice hypotheses.
4. `pressureOfVelocity_slice_smooth` proves spatial `C∞` of every pressure
   slice using the compact-parameter integral theorem.
5. `pressure_smooth_of_velocity_smooth` proves c4 from the explicitly named
   additional global, endpoint-compatible regularity hypothesis

   ```lean
   hjoint :
     ContDiff ℝ ∞ (pressureGradientOfVelocity ν f velocity)
   ```

   by differentiating the radial integral jointly in `(t,x)`.  This hypothesis
   is not implied by c3 plus `MemForceR`; B1/T1 must still supply an
   endpoint-compatible version.
6. `momentum_of_projected` uses
   `A01.navierStokesResidual_eq_iff_projected`: joint velocity smoothness
   supplies spatial differentiability and `hdiv` supplies incompressibility.
   Once the explicitly defined `G = R - ∂ₜu` is smooth and curl-free, the
   pointwise identity needed by the equivalence follows algebraically from
   `convectionDivergence_eq_advection` and the definitions.  The genuine
   mild/Leray projected input is the datum equality used by
   `pressureGradient_pressureOfVelocity_lerayComplement`.

All declarations have exactly the standard axiom footprint
`[propext, Classical.choice, Quot.sound]`.

## Inventory and rejected routes

The complete prescribed search over
`Section4/{D01,A03,A04,A01,C01}` found only the direction

```lean
curl-free physical field -> longitudinal datum
```

in `D01/Longitudinal.lean` and `D01/OrderZeroCurl.lean`; it found no converse
turning the output of `Leray.lerayComplement` into a pointwise smooth,
symmetric-Jacobian physical field.  Therefore defining `p` by choosing a
physical representative of an arbitrary Leray datum would merely hide a new
realization theorem inside a choice.

The existing pin
`D01.isSobolevDatum_pressureGradient_lerayComplement` cannot be used in the
constructor: its first argument is already
`u : A02.ClassicalSolutionR ν a f T`.  That would be circular while assembling
c4/c9.  It is nevertheless the exact consumer-side counterpart of the datum
identity proved here.

The HeliCorgi scalar `r3HelmholtzPressure` route was not used.  Its gradient
theorem is distributional and complex/cycles-normalized, so this lane would
still owe the real angular-datum and distribution-to-pointwise bridge before
the radial potential theorem could apply.

## Remaining named inputs

This module closes the pressure assembly after the following facts have been
transported from the mild candidate.

- Per time `t`, spatial smoothness and
  `RadialPotential.HasSymmetricJacobian` of
  `pressureGradientOfVelocity ν f velocity (t,·)`.  The latter is the
  pointwise curl-free conclusion of the Helmholtz projection.  The tree has
  the forward implication (curl-free gives a longitudinal datum), not the
  reverse implication needed here.
- Per time `t`, `MemLp` for the residual and `∂ₜvelocity`.
- The datum-form projected equation displayed above.  This is the exact
  order-zero carrier statement required by
  `pressureGradient_pressureOfVelocity_lerayComplement`.
- For c4, the additional global, endpoint-compatible joint hypothesis
  `ContDiff ℝ ∞ (pressureGradientOfVelocity ν f velocity)`.  The supplied
  c3 `ContDiffOn` velocity hypothesis on the half-open slab together with
  `MemForceR` does not imply this global statement: the current open-domain
  regularity API does not control the upstream two-sided `fderiv` used by
  `temporalDerivative` at `t = 0`.  B1/T1 must still prove an
  endpoint-compatible version.

The attempted direct use of
`NavierStokes.ResidualRegularity.contDiffOn_temporalDerivative` on the
half-open slab failed with:

```text
/dev/stdin:10:4: error: Application type mismatch: The argument
  IsOpen.prod isOpen_Ioo isOpen_univ
has type
  IsOpen (Ioo ?m.55 ?m.56 ×ˢ univ)
but is expected to have type
  IsOpen (Ico 0 T ×ˢ univ)
in the application
  NavierStokes.ResidualRegularity.contDiffOn_temporalDerivative (IsOpen.prod isOpen_Ioo isOpen_univ)
```

This is why the joint input is stated rather than silently inferred from
half-open-slab smoothness.  It belongs with the unfinished B1/T1 time
regularity ladder.

## Contract-closure follow-up

`ConstructorPressure` is currently in no registered contract closure, so
`make test` does not compile it.  It must join the next registered A01 contract
closure after merge.

## Non-vacuity

`pressureOfVelocity_zero` proves for every `ν` that zero force and zero
velocity give exactly the zero pressure.  The same statement is repeated as
an `example` in `axioms_pressure_p3.lean`.
