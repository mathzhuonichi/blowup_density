# T23 U5 domain comparison — attempts

This file records failed proof and gate attempts verbatim as development
proceeds.

## 1. Rewriting compactness at an applied theorem name

The first comparison build tried to rewrite an equality directly “at” an
applied theorem expression:

```text
error: NSFormalization/Section3/T23/DomainComparison.lean:69:48: Unexpected term `prescribed_closedBall_compact`; expected single reference to variable
```

The successful form rewrites the goal with `closure_ball c hR.ne'` and then
applies `prescribed_closedBall_compact c R`.

## 2. Probe velocity-field namespace

Importing the registered T22 contract also made its historical packet field
abbreviation available.  The first probe used an unqualified `VelocityField`,
so the placement parameter selected the wrong abbreviation:

```text
../research/T23/probes/T23-U5-domain-comparison_closes.lean:88:47: error: Application type mismatch: The argument
  u
has type
  VelocityField
but is expected to have type
  NavierStokes.ProblemStatement.VelocityField
in the application
  DomainPlacementData u
```

The probe now qualifies all three raw placement field types through
`NavierStokes.ProblemStatement`.  The accompanying
`declaration uses 'sorry'` diagnostic was Lean's recovery from this type error;
there was no proof admission in the source.

## 3. Successful route

For each Sobolev order, `norms.zeroExtensionComparison` is specialized once to
`K = closure (Metric.ball c R)`, before introducing either time or `ε`.  U3's
exact `forceDifference_mem` type yields smooth spatial slices by choosing the
closed slab `Icc 0 t`.  U4's pointwise nonvanishing support yields the T22
`tsupport` premise by `closure_minimal` and closedness of `K`.  Both pointwise
inequalities are integrated with `setLIntegral_mono'`; the upper inequality is
then factored with `lintegral_const_mul'`.  This route makes no measurability or
finiteness assumption on either extended norm.

The final standalone checks for both modules and the probe produced zero
output.  The axiom audit printed exactly
`[propext, Classical.choice, Quot.sound]` for all nine production theorems.
