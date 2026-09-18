# T22 U-B2 attempts

## Closed route

`zeroExtension Ω z` unfolds to `Ω.indicator z`.  At a point of the open set
`Ω`, it is eventually equal to `z`, so `ContDiffOn.contDiffAt` and
`ContDiffAt.congr_of_eventuallyEq` give smoothness.  At a point outside `Ω`,
the support inclusion `tsupport (zeroExtension Ω z) ⊆ K ⊆ Ω` puts the point in
the open complement of the closed support; there the extension is eventually
equal to the zero field.  This proves global `ContDiff` pointwise.  The compact
support statement is obtained with `HasCompactSupport.intro` and the same
support inclusion.

Mathlib's `HasCompactSupport.iteratedFDeriv` then gives compact support for
every spatial jet.  Each jet is continuous by
`ContDiff.continuous_iteratedFDeriv`, hence belongs to `MemLp` by
`Continuous.memLp_of_hasCompactSupport`.  This supplies the local
`SmoothSquareIntegrableJets` predicate, and D01's
`exists_isSobolevDatum_of_contDiff_memLp` produces a datum at every real order.

## Failed intermediate attempt

The first version passed `hsupp : tsupport (zeroExtension Ω z) ⊆ K` directly as
the second argument of `HasCompactSupport.intro`.  In this Mathlib pin that
argument is instead the pointwise zero-on-`Kᶜ` condition.  The final proof
derives that condition by contradiction: a nonzero value would put the point
in the closed support, contradicting `hsupp` and the point’s membership in `Kᶜ`.

No `sorry`, `admit`, `axiom`, or `native_decide` is used.

## Continuation verification

The recovered main module elaborates without changes. The probe now also
checks nonvanishing of the vector zero extension at the origin, compact
support, and the full smooth-jet predicate. The initial nonvanishing proof
reported `Invalid field ne_zero: The environment does not contain
OrthonormalBasis.ne_zero`; use the underlying `toBasis.ne_zero` instead.
