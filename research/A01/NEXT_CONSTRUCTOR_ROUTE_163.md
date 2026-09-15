# Next constructor route: same-horizon all-order tower (lane 163 audit)

## Lane 166 update

The recommended first step below is now proved in
`formalization/NSFormalization/Section4/A01/ForcedMaximalRegularity.lean`.
The actual nonlinear mild equation supplies a compatible higher TimeLp path
on the same fixed-q horizon. The real MemForceR consumer preserves the input
force slices and ordinary initial datum. Module, five axiom audits, 26 existing
contracts and mutations passed; see `logs/VALIDATION_166_20260915.md`.

The remaining analytic gap described below is unchanged: continuous higher-order
persistence on a common low-order horizon, then a compatible all-order tower
and the time-smoothness bootstrap. A.e. time-L2 regularity supplies neither
endpoint values nor a continuous higher-order path. The historical audit below
records the source review before lane 166 and is retained for context.

## Conclusion

The inspected spine does not yet construct a compatible all-order tower from a
single finite-q nonlinear mild path. Reusing the classical higher-energy results
to manufacture that tower would be circular. There is, however, a direct,
non-circular one-order **Bochner L2-in-time** gain already proved in vendor code.
This is weaker than the continuous realizations a SobolevTower requires.
No Lean source was changed and no Lean command was run for this audit.

## Direct mild results already available

- `Source/OrdinaryForcedLocal.lean:32`, `exists_local`: finite-q forced mild
  solution and ordinary path, genuine equation/angle/divergence constraints.
  The positive horizon depends on q; applying it separately at each order does
  not produce a common positive horizon.
- `A01/Horizon.lean:137`, `localTheory_on_prescribed_horizon`: a prescribed S is
  obtained only from `HasAprioriBound` (`:106`), which demands a uniform bound on
  every partial solution at that same q. No order-uniform bound is proved there.
  Its source is `Euler/BoundedMildContinuation.lean:39`,
  `exists_global_mild_of_bound`, with the same explicit bound premise.
- `Source/OrdinaryForcedTime.lean:36`, `ordinary_hasDerivAt`, and
  `realization_hasDerivAt`: actual Duhamel equation gives the ordinary L2 time
  derivative. `ordinaryDerivative_continuous` constructs its continuous values.
  `Source/OrdinaryForcedEvolution.lean` merely bundles/clamps that derivative
  path; it is not a higher spatial-order or all-time-derivative bootstrap.
- **Important extra supply:** `Euler/SobolevMaximalRegularity.lean:45`,
  `viscous_mild_maximal_regularity`, constructs `TimeLp S (SobolevSpace 1 (q+2))`
  from a continuous H^(q+1) mild path with continuous H^q source, and identifies
  its restriction with the original path a.e. in time. `viscous_mild_ae_higher`
  (`:59`) gives per-time higher membership only a.e. `HeatMaximalRegularity.lean:92`
  is its H1-to-H2 special case. These are actual approximation/completion proofs,
  not classical-solution adapters.

## Available adapters and where they stop

- `Euler/HeatAllOrders.lean:18`, `cylinderHeat_all_orders`: positive-variance
  heat of an L2 datum is in every spatial order. `smoothApprox_representative_all`
  supplies smooth approximations. Neither proves that a nonlinear Duhamel
  solution has all orders: the Duhamel time lag reaches zero, and smoothing
  estimates can blow up there. Nor do these results give approximation-index
  uniform high-order bounds as the smoothing variance tends to zero.
- `Euler/OrdinarySobolevTower.lean:23`, `SobolevTower`, **takes** every continuous
  realization on the same S and the common lifted L2 value. Its `smoothField`,
  `smoothField_toLp`, `smoothField_jet_continuous` and `smoothField_realization`
  then genuinely reconstruct compatible spatially smooth representatives.
  Equality of the underlying L2 value, not a separately assumed collection of
  jet identities, is enough for this compatibility. The tower itself is missing.
- `Euler/OrdinarySmoothLimit.lean:34`, `nonempty_smoothLimitData`, builds the
  tower from smooth approximating paths only if they are L2-Cauchy and have
  `∀ q, ∃ Mq, ∀ k t, tensorNorm q (A k t) ≤ Mq` on the same interval.
  Those uniform high-order bounds are a substantive input, not a conclusion.
- `C01/JetPaths.lean:86–99`, `forcePath`, `forcePath_field`,
  `forcePath_jetLp_continuous`, supply the actual force path from `MemForceR f`
  without assuming a solution. Keep the stronger original `hf` for the later
  time-smoothness bootstrap; the continuous projection alone loses information.

## Circular routes and remaining analytic content

`A01/AprioriRows.lean:199,219` higher-order bounds require both an existing
`ClassicalSolutionR` and `HasSmoothSobolevPath`; so do the underlying
`A01/GronwallInstance.lean:68,115` results. They can estimate a completed classical
solution, not construct its missing all-order regularity. `A01/Propagation.lean`
`higherOrder_bddAbove` and `higherOrder_bddAbove_fixedDriverSq` are scalar
Grönwall packages requiring each order's continuous energy and integral step.
Calling them does not supply those PDE inequalities. The vendor
`OrdinaryEulerHigherEnergy.Evolution.integer_energy_bound` likewise assumes an
already smooth Euler Evolution with continuous all-order velocity/derivative
jets; it is not forced-viscous finite-q persistence.

The real gap is a finite-mild/regularized energy argument yielding continuous
higher-order persistence (or uniform smooth-approximation bounds) on the
low-order horizon. One must also align higher/lower forcing, heat, projection,
and nonlinear operators under restriction. Local `VolterraUniqueness.mild_solution_unique`
works inside a contraction ball; using it across orders/whole S needs the actual
restriction and window argument. Independent high-order local horizons cannot
simply be intersected: their infimum may be zero. A same-S tower would still need
force time-smoothness and a time bootstrap before joint C∞ follows.

## Recommended smallest next subtask

**Wire the actual forced Duhamel witness into the existing maximal-regularity
supplier, without assuming a classical solution.** For the current u, package
its continuous H^q source as
`G(t) = (coefficients 1 hq (sobolevPath F hF q)).apply t (u t)`
on S (include `timeInclusion` on shorter windows). Unfold
`Euler/QuadraticHeatLocal.lean:23` `quadraticDuhamel` to obtain exactly the linear
Duhamel hypothesis of `EulerSobolevMaximalRegularity.viscous_mild_maximal_regularity`.
Return its genuine `TimeLp S H^(q+2)` element and a.e. restriction equality to u,
with F identified with the actual `MemForceR` slices. This is a small real new
supply result on the unchanged horizon, not a generic interface or new premise.

Do **not** label this a SobolevTower: it supplies the first non-circular higher
spatial derivative in time-L2. The subsequent analytic subtask is upgrading that
supply to a continuous one-order lift through a finite-order tame energy or
regularized approximation estimate. No inspected theorem automatically iterates
the L2-in-time result to the continuous all-order tower.
