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
