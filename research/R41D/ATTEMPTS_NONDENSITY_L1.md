# Lane 224: L¹ non-density

## Successful proof

`Section4/R41/NonDensityL1.lean` proves the exact zero-datum non-density
predicate of `Contracts/V1/Data.lean:672–708`, with the canonical D01
path-infimum norm. The excluded radius is `R43.criticalConst * ν`.

The existing `D01.isSobolevPath_lower` preserves all slice-datum clauses.
Continuous linearity preserves strong measurability (and `comp_memLp'`
already preserves any available Lq membership). Only measurability is required
by the norm's admissible subtype. Applying `eLpNorm_mono` to each lowered
path and then `iInf_le` / `le_iInf` proves order monotonicity for arbitrary
q, real orders, and physical forces, including empty path families.

For the constant-one bound, factor angular lowering through the unitary
`angularFrequencyDilation`. Its middle multiplier is
`sobolevBesselWeight (r-s) (frequencyUnit • ξ)`, whose norm is at most one
when r ≤ s. `Lp.norm_le_norm_of_ae_le` proves scalar contraction; summing
component norm squares proves contraction on `RealVectorSobolev`.

The endpoint theorem makes every small force global. Membership in the
breakdown set bounds the lifespan by `ofReal T`, which cannot be top.
Order monotonicity transfers the lower bound to every s ≥ 1/2. Relative
density at the zero force would produce a force both below and above the
same positive radius, a contradiction.

## Rejected routes and compilation corrections

- `A03.norm_lowerDatum_le` has the coarse factor `lowerConst s r`, not one.
  Using it would lose the requested exact radius. The unitary multiplier
  representation above avoids this loss; no new analytic premise is needed.
- Opening all of A02 and D01 made `MemForceR`, `IsSobolevPath`, and
  `forceTimeMeasure` ambiguous. Restricting the A02 open list resolved this.
- An initially reversed `top_le_iff` equality was corrected.
- A direct `rfl` bridge for lifespan-dependent sets is unavailable because
  A02 and Contracts have separate `ClassicalSolutionR` structures. The
  existing `Bindings.maximalPartial_maximalLifespanR_eq` bridges them.
  Force-class and relative-density definitions themselves bridge by `rfl`.

## Fidelity and scope

No earlier `breakdownSetR` / `RelativelyDense` copy exists in Section4.
Their new local definitions reproduce the Data bodies with cited line numbers.
The norm reuses D01.HalfOrder rather than adding another copy.
The conformance file proves the final results in literal Data vocabulary.

`research/R41D/Spec.lean` uses literal thresholds and has no exponent field.
Thus no new ThresholdAPI-shaped object is introduced. The module documents
`ThresholdAPI.l1` at zero and `energy` as the arithmetic source of 1/2.

No named hypothesis remains. Non-vacuity examples show zero in the ambient
force class and instantiate the conclusion at ν = T = 1, s = 1/2.
No claim is made that a breakdown force exists.

The new-files-only ground rule conflicts with the requested edit to the
existing COMPARISON.md. Its lane update is supplied as the new companion
`COMPARISON_NONDENSITY_L1.md`; no existing file is modified.
