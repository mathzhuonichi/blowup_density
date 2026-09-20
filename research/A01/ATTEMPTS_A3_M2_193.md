# Lane 193: the base-order-radius route

## Result and remaining analysis

`AprioriFamily.lean` proves the base a-priori bound, time-prefix uniqueness
(including `T = 0`), higher-to-base identification, the physical H² cap transfer,
and the conditional all-order bound family. No all-order constructor occurs in
these proofs. The sole PDE input in `hb_of_base` is `MildGronwall`, stated as an
integrated finite-order energy-envelope inequality, **not** as the desired
uniform bound. Scalar Grönwall is proved in the tree and is applied here.

The envelope formulation matters: the cylinder norm is a supremum of word
norms, whereas the energy estimate uses a Hilbert Sobolev norm. It would be
unjustified to assert its differential inequality verbatim for the cylinder
norm. `E q` accounts for both norm comparisons and the forcing comparison;
`C q` is the energy coefficient at the fixed viscosity. Both are fixed before
all windows and all competitors. Their admissible choices, and the PDE
inequality, remain to be supplied by finite-order energy analysis.

The explicit radius is

```
R q = E q * (‖ordinarySobolev (q+1) a.toLp a.translation_contDiff‖
               + S * ‖sobolevPath F hF (q+1)‖)
          * exp (C q * (256 * R₆^2 * S)).
```

This deliberately uses the same-order force `H^{q+1}`, with its L¹ time norm
bounded by `S` times its continuous-path sup norm. It is a conservative explicit
bound, not the sharp L¹ expression. The suggested `L¹H^q` input cannot simply
be substituted into the `H^{q+1}` energy estimate; gaining a derivative by the
heat kernel requires a different time estimate. Smooth forces provide the
higher norm used here.

## What the vendor actually provides

`Euler.QuadraticHeatLocal.exists_local_quadratic_mild` at `q = 6` supplies
`0 < S₆ ≤ Smax`, a continuous path in `SobolevSpace 1 7`, its initial value,
the actual Duhamel fixed-point identity, and the radius
`R₆ = ‖ordinarySobolev 7 a.toLp a.translation_contDiff‖ + 1`.
No a-priori bound is an input to this local theorem. Our `exists_base_apriori`
turns that output into `HasAprioriBound` for the force restricted to `[0,S₆]`.
It does not claim a data-independent horizon.

There is **no closed-form lifespan definition in this vendor theorem**.
Writing `P` for its coefficients, its proof chooses a positive time satisfying

```
mass(T) = T + 2 * parabolicConstant ν * sqrt(T)
parabolicConstant ν = gaussianAbsMoment 1 / sqrt(2 * ν)
M = P.ballBound R₆
  = ‖P.projection‖ * (‖P.forcing‖ + ‖P.linear‖*R₆ + ‖P.quadratic‖*R₆^2)
L = P.ballLipschitz R₆
  = ‖P.projection‖ * (‖P.linear‖ + 2*‖P.quadratic‖*R₆)
mass(T)*M < 1, mass(T)*L < 1, 0 < T ≤ Smax.
```

`VolterraUniqueness.exists_positive_time_budget` obtains an `ε` from a
neighborhood of zero and uses `T = ε/2`; it is an existential choice with these
budgets. Claiming a vendor formula such as `c/R₆²` would misstate this interface.

`UniformHeatLocal.exists_uniform_restart_time` chooses `δ` using the same
budgets with `ballBound (R+1)` and `ballLipschitz (R+1)`. Every restart datum
of norm at most `R`, every permitted offset, and every duration at most `δ`
then admit a solution bounded by `R+1`.
`BoundedMildContinuation.exists_global_mild_of_bound` pastes finitely many
such windows, but **requires** a bound for every partial fixed point. It
cannot supply the missing a-priori bound by itself.

## Search and negative routes

Searched all of `Section4/{D01,A03,A04,A01,C01}` for Grönwall, high continuation,
and derivative identities, in addition to the vendor local/continuation files.
`A04.Gronwall.gronwall_integral_mul` is carrier-independent and is reused.
`A04.HighEnergy` contains datum/inner-product assembly, but
`A04.EnergyIdentityHigh.energyIdentityHigh_core` and `energyIdentityHigh`,
`A04.HighContinuationIntegral`, `A01.GronwallInstance`, and
`A01.GronwallEndpoint` require a `ClassicalSolutionR`.
`A01.DatumPathDeriv.exists_differentiable_datumPath` differentiates at
`m ≤ q-1`; it does not directly yield the energy identity at `m = q+1`.
Thus the search does not discharge top-order finite-order mild energy analysis.

A diagnostic attempt to pass an order-six continuous mild path as `w` gave:

```
error: Application type mismatch: The argument
  u
has type
  C(↑(Icc 0 1), ↥(SobolevSpace 1 7))
but is expected to have type
  NSFormalization.Section4.A02.ClassicalSolutionR ?m.16 ?m.17 ?m.18 ?m.19
in the application
  highOrder_bddAbove_of_kbnd hν✝ ha✝ hf✝ hf1✝ u
```

Other rejected routes:

* Feeding the sought all-order family into a smooth constructor first is
  circular and is not used.
* Using the high-order competitor's own radius in `256*R²*S` makes the
  exponential depend on the radius being proved; lowering replaces it by `R₆`.
* Whole-positive-window uniqueness alone omits the `T = 0` case quantified by
  `HasAprioriBound`; `quadratic_mild_unique_window` proves it separately.
* The physical cap alone is not a mild energy inequality: invariance, ordinary
  descent, slice agreement, and norm continuity are explicitly retained in
  `h2_cap_transfer` rather than silently constructing a classical solution.

The requested file `research/A01/REVIEW_192-A01-wiring-hsob.md` is absent:
`sed: can't read research/A01/REVIEW_192-A01-wiring-hsob.md: No such file or directory`.
Lane 192's committed export was inspected with `git show` on
`erenup/192-A01-wiring-hsob`. `CylinderWiring.lean` is not in this checkout;
`probe193_wiring.lean` copies the full combined `constructorInputs_of_bounds` statement at `9ca0a45` as a
theorem parameter and checks the exact application of `hb_of_base`.
This is an interface probe, not a claim that the sibling module was imported.

## Satisfiability of named inputs

The algebraic/type parameters are ordinary data; the following lists every
substantive property supplied to the exported results.

* `hq`: restricting the finite Sobolev order to `q ≥ 6` is precisely the vendor
  local theory's regularity range for genuine solutions.
* `hν`: positive viscosity is the standard Navier–Stokes parameter restriction.
* `hS`, `hT`, `hTS`: nonnegative horizons and included subwindows restrict a
  genuine positive local existence interval, including its singleton prefix.
* `hF`: continuity of every force jet holds for the paper's smooth force when
  restricted to the compact local interval.
* `h₆` and `hu`: these are exactly the genuine forced Duhamel identities at the
  stated finite orders, with the same initial datum and force.
* `hR`: the base solution's finite sup bound is provided by the vendor's
  nonzero-data local existence theorem with radius `‖a₆‖+1`.
* `hE`: nonnegativity is a restriction of the positive finite-order norm
  equivalence constants used to dominate energy and forcing norms.
* `hC`: nonnegativity is a restriction of the usual positive high-energy
  coefficient depending on order and viscosity.
* `hMG`: on a genuine finite-order solution, the standard integrated Sobolev
  energy estimate supplies a continuous scalar envelope dominating the
  cylinder norm; norm equivalence gives its initial bound and same-order
  forcing bound, and the H² comparison bounds its driver by the displayed
  `256*‖lower₆ u‖²`; proving this transfer at finite regularity is the open unit.
* `hi`: angular invariance is the standard invariant lift of an ordinary
  nonzero solution and is preserved by the forced local solver.
* `hl`: equality with the restricted base path is the ordinary uniqueness
  property and is proved by `lower_identification`.
* `hU`: ordinary-lift agreement is the standard cylinder-to-ordinary descent
  relation of an invariant solution.
* `hslice`: almost-everywhere slice agreement is the standard choice of a
  physical representative of that ordinary L² path.
* `hcont`: continuity of the physical H² norm on the local interval follows
  from a continuous H² solution path and is only restricted to `Ico` here.
* `export192` is solely the copied sibling theorem in the composition probe;
  after integration it is supplied by `hsob_of_bounds hf hν hS a ha`, with
  `hf` the standard smooth force class and `ha` the solenoidal datum property.

No assumption forces endpoint stationarity or time-clamps a solution beyond
its own horizon. The non-vacuity example proves `hMG` for zero data on `[0,1]`
for **every** `q ≥ 6`, by unrestricted uniqueness, then invokes `hb_of_base`.
This test is in addition to the nonzero-solution satisfiability explanations,
not a replacement for them.

## File policy and validation

The requested `ATTEMPTS_A3_M2.md` and `axioms_a3_m2.lean` already belong to lane
142. Its Lean audit is preserved unchanged under the no-existing-module-edits
rule; the new complete audit is `axioms_a3_m2_193.lean`. This record is linked
from the existing attempts document and the A3-M2 row as requested.
All 11 module declarations and all three named audit helpers print exactly
`[propext, Classical.choice, Quot.sound]`. The module and composition probe
check with zero output. Gate results and exact declarations are in `REPORT_193.md`.
