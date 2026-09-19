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
