# Lane 232: combined `q ∈ {1,2}` non-density

## Successful assembly

`Section4/R41/NonDensity.lean` combines lanes 224 and 229 by cases on the
real exponent `q`.  For `q = 1`, `RMainThresholds.l1` turns the threshold
hypothesis into `1/2 ≤ s`, and the witness is explicitly
`R43.criticalConst * ν`.  For `q = 2`, `RMainThresholds.l2` turns it into
`-1/2 ≤ s`, and the witness is explicitly `R44.radius ν T`.  The same split
applied to `not_breakdownDenseR_zero_L1` and
`not_breakdownDenseR_zero_L2` proves the exact failure of relative density.

The proposed `RMainAPI` fixes `q : ℝ`, while the implemented
`forceSobolevENorm` takes `q : ℝ≥0∞`.  The combined statements retain the
skeleton's real binder and use `ENNReal.ofReal q`.  This is total for an API
binder and reduces to the literal existing norm exponent in both permitted
cases: `ofReal 1 = 1` and `ofReal 2 = 2`.  Changing the theorem binder to
`ℝ≥0∞` would make the norm application shorter but would no longer mirror
the skeleton or its real-valued `ThresholdAPI.exponent`.

The formalization package cannot import the downstream verification package.
Consequently `RMainThresholds` copies the frozen `ThresholdAPI` field shape,
including the formula
`exponent q s = 2 / q - 3 / 2 - s` verbatim.  Its canonical value uses
`Paper3.forceExponent`, exactly as `Bindings.thresholds` does.  The
conformance audit supplies both a conversion from any frozen
`Contracts.V1.ThresholdAPI` and an `rfl` equality between the canonical local
and registered exponent projections.

`RMainNonDensity` keeps the skeleton binder order
`ν, T, hν, hT, q, hq, thresholds` and only the proved `nonDensityZero` field.
It intentionally contains no density or regular-reference field.  Concrete
instances at `ν = T = 1` for both `q = 1` and `q = 2`, plus both corresponding
negated-density examples, check non-vacuity.

## Rejected routes and compilation corrections

- Taking `q : ℝ≥0∞` in the combined API was rejected because the proposed
  `RMainAPI` and threshold exponent both take real `q`; it would require a
  different threshold record or repeated coercion in the opposite direction.
- Hard-coding `1/2` and `-1/2` directly in the combined theorem was rejected.
  Both endpoints are obtained through the supplied threshold record's `l1`
  and `l2` fields, so an arbitrary malformed exponent function cannot pass.
- Merely forwarding the endpoint existential theorems was avoided in the
  main proof: each case constructs its requested radius directly, making the
  witness visible in the combined theorem.
- Writing the dependent structure fields as one declaration `ν T : ℝ`
  triggered a Lean 4.34 elaboration failure in the later nested function
  field (`ν` was inferred as a function).  Splitting these into the two
  equivalent declarations `ν : ℝ` and `T : ℝ` preserves the skeleton and
  elaborates reliably.
- A direct `rfl` bridge for the breakdown sets remains impossible because the
  local and contract `ClassicalSolutionR` structures are distinct.  The
  conformance proof reuses
  `Bindings.maximalPartial_maximalLifespanR_eq`, as the endpoint audits do.

## Scope

This lane proves only Theorem 4.1(ii)'s non-density/only-if half at zero
initial velocity.  It does not claim `densityFixedInitial`, `densityZero`, or
`regularReferenceRider`, and it does not register a full `RMainAPI` contract.
