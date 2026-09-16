# Lane 219 — critical time smoothness and momentum

## Successful route

1. `D01.Homogeneous.isHomogeneousSliceDatum_unique` already proves uniqueness
   at every real order. No new Fourier injectivity argument is needed. Applied
   to lane 216's converted datum, it identifies `chosenHomogeneousDatum` with
   `ofSobolevVectorL ∘ lowerVectorL` on every represented slice.
2. `BesselFractionalData.datum` is already complex continuous linear and
   contractive. Corestricting it to the real subspace gives `ofSobolevScalarLM`
   and `ofSobolevScalarL`; the finite product construction gives
   `ofSobolevVectorL`, definitionally equal to lane 216's `ofSobolevVector`.
3. The baseline does **not** contain `A04/RestartFixedForce.lean` or
   `research/A04/REPORT_215.md`. Both were inspected using `git show` on the
   available local branch `erenup/215-A04-restart-fixed-force`. The seven
   declarations through `classical_hasSmoothSobolevPath` are reproduced in the
   new module under `R43.CarrierWindow`, with imports and open namespaces
   adapted. No merge, rebase, branch change, or existing-module edit is needed.
   Fixed-force uniformity and a compact H⁷ bound choose a backward restart
   point. Velocity uniqueness and datum uniqueness identify the arbitrary
   solution with the same local carrier on a neighborhood of the target time.
   Carrier smoothness transfers on these neighborhoods, including the
   one-sided neighborhood at zero.
4. Use order **two**, rather than order one, for the smooth datum path.
   `A04.TimeDerivative.timeDeriv_isSobolevDatum` and
   `A04.MomentumDatum.momentum_datum` already prove exactly the integer-order
   derivative identification needed when `2 ≤ m`. All four order-two residual
   data exist by smooth square-integrable jets; D01 pressure regularity supplies
   the pressure-gradient jets under `MemForceR`.
5. `orderTwoToHalf` composes continuous linear order lowering and homogeneous
   conversion. Its composition with the smooth order-two path equals the
   chosen half-order path on `Ico 0 T`. Continuous linear differentiation and
   equality on a neighborhood give its derivative. Applying the same map to
   `momentum_datum` and identifying the four terms by uniqueness proves
   `criticalVelocityHalf_momentum`.
6. Assemble both fields of lane 216's unchanged `CriticalDatumInputs` and use
   its existing consumers. All three requested final theorems have only
   positive viscosity, force membership, and the arbitrary classical solution
   as inputs. There is no residual named analytic hypothesis.

## Alternatives inspected

`ManuscriptLocalRegularity.projected` is a physical pointwise momentum
statement, not a datum derivative. Lane 169's residual derivative plus
lanes 189/195/197 is a valid longer route, but unnecessary here: the existing
A04 datum derivative theorem applies after the smoothness transfer. There is
no circular construction of a classical solution; the theorem starts with
an arbitrary classical solution and derives its additional path regularity.

The more general homogeneous uniqueness requested in the brief was already
present in `D01/HomogeneousWitness.lean`; it is reused rather than duplicated.
The general `chosenHomogeneousDatum_eq` also covers order-one-to-half lowering
and the other homogeneous slice choices whenever their Sobolev data are given.

## Elaboration issues and their fixes

- Scalar contractivity initially reported a type mismatch between subtype
  norms and ambient Fourier norms. An explicit `change` to ambient norms fixes
  the definitional coercions.
- Opening both D01 and A02 makes `MemForceR` ambiguous. Public theorem binders
  explicitly use `A02.MemForceR`.
- `Filter.nhds` does not exist; the neighborhood filter is `nhds`.
- Generic `rw [map_add, map_sub, map_smul]` searched unrelated algebra
  instances on the Sobolev subtype and exhausted even 400000 heartbeats.
  Specifying `orderTwoToHalf.map_add`, `.map_sub`, and `.map_smul` removes
  that search. The final proof still exceeds the default 200000 budget and
  uses a documented declaration-local 400000 budget. Four final slice equalities are combined directly with
  `congrArg₂`, avoiding rewriting inside classical datum choices.

## Scope and non-vacuity

The zero-force `A04.zeroSol 1 2` instance consumes the unconditional theorem
in `axioms_critical_momentum.lean`; it does not assume the conclusion. Since
there is no residual hypothesis, no artificial restriction to stationary or
zero solutions is introduced. Smoothness is on `Ico 0 T`, and momentum is only
on `Ioo 0 T`; no two-sided derivative at zero or continuation at T is claimed.

S1/G7 is closed. Lane 216's G3 result remains slicewise: a measurable integrable
homogeneous force path, its time primitive, and the later bootstrap are
separate obligations. No contracts or existing Lean modules were modified.
