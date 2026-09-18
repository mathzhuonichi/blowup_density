# T17 U5/U6 attempts — concrete derivative bounds

## Successful route

For each derivative order, `correctionDerivConst` and `forceDerivConst` are
`Classical.choose` projections of the corresponding Paper1 existence theorem:

- `CorrectionProfile.physical_mixed_derivative_bound`;
- `CorrectionForceProfile.physicalForce_spatial_derivative_bound`.

For the correction, `physical_support` supplies the all-time spatial-slice
support in `ball x₀ (ε * θR)`.  The placement hypotheses give
`ε * θR < r` and, from `r < 1/2`, `r + ε * θR ≤ 1`.  Therefore
`latticeLift_iteratedFDeriv_eq` selects a lattice vector `k` at every spacetime
point, including the no-copy case.  After `correctionData_correction`, the
lifted derivative norm is exactly the Euclidean derivative norm at
`z - (0, latticeVector k)`, where the Paper1 bound applies.

For the force, `force_eq` first rewrites the T17 force to the lattice lift of
the Euclidean `Source.correctionForce`.  Its slice support follows from
`Source.LocalizedInsertion.correctionForce_support` and `physical_support`.
The same derivative bridge and the Paper1 force bound then close the field.

Both Paper1 theorems require global `hv : ContDiff ℝ ∞ v`; consequently both
T17 theorems carry that premise.  In U6 it also discharges `force_eq`'s local
smoothness premise via `hv.contDiffOn`.  The placement-side premise
`ε₀ ≤ 1` converts `ε ∈ Ioc 0 ε₀` to the Paper1 range `Ioc 0 1`.

## Failed elaborations retained verbatim

The first correction statement omitted parentheses around the projected
function `(correctionData ...).correction ε`.  Lean consequently parsed the
applications at the wrong level:

```text
error: NSFormalization/Section3/T17/CorrectionDeriv.lean:57:65: Application type mismatch: The argument
  z
has type
  SpaceTime
but is expected to have type
  Fin (j + m) → ℝ
...
error: NSFormalization/Section3/T17/CorrectionDeriv.lean:56:13: failed to synthesize instance of type class
  NormedAddCommGroup SpaceTimeField
```

Adding the missing parentheses fixed the statement without changing it
mathematically.

The support theorem was imported but not opened under its defining namespace:

```text
error: NSFormalization/Section3/T17/CorrectionDeriv.lean:71:11: Unknown identifier `physical_support`
error: NSFormalization/Section3/T17/ForceDeriv.lean:85:11: Unknown identifier `physical_support`
```

Opening `NSFormalization.Source.PhysicalRemoval` exposed the exact theorem.

The first nonzero-reference probe attempted to rewrite a scalar coordinate
goal directly with a vector equality:

```text
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  v (0, 0)
in the target expression
  (coordinateVector 0).ofLp 0 = 0
```

Unfolding the local constant field in the vector equality first, then taking
its zeroth coordinate, proves the contradiction.

## Residual

There is no residual proof obligation in U5 or U6.  Assembly still has to
supply the already-recorded global-smoothness premise `hv` and the placement
inequality `D.ε₀ ≤ 1`; these are not derivable from the current abstract
`CorrectionAPI` fields alone (the same G1 issue recorded by U3).
