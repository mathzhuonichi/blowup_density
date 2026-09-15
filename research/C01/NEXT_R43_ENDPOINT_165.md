# Next R43 endpoint step after C01 V4 (lane 165)

The existing R43 G5 is now a concrete consumer task. Frozen
`Contracts/V2/MaximalPartial.lean` defines `IsMaximalSolution` by a positive
extended-real lifespan and, for every positive r strictly below it, an actual
`ClassicalSolutionR ν a f r` whose velocity and pressure equal the supplied
fields. This is stronger than merely having unrelated local solutions.

Recommended next proof: for that actual maximal family, actual initial/force
classes and positive viscosity, assume the C01 absorption bound throughout the
presingular times. Prove the same C01 H² lower-integral estimate for every real
0<S with ofReal S ≤ maximalLifespanR, including equality at a finite maximal
lifespan. No continuation, new critical energy estimate or maximal-family
existence theorem should be assumed or claimed beyond the supplied existing
IsMaximalSolution predicate.

For every 0<r<S, ofReal r is strictly below the maximal lifespan. Its supplied
classical solution allows V4.h2TimeIntegral with integration endpoint r and
solution horizon r. The resulting bound is uniformized to S using actual
force regularity, monotonicity of energyBudget/force-square integral, and
nonnegative coefficients. A countable directed union of Ioo 0 r then covers
Ioo 0 S. This never requests a classical solution at S or a value of velocity
at the singular endpoint. Existing C01.h2TimeIntegral_Ioc and
lintegral_Ioo_le_of_Ioc are implementation-level alternatives; the public V4
Ioo bound is enough, using a slightly larger inner r when necessary.

Keep the canonical angular sobolevENorm and the existing natural-square /
real-power equality for the A04 squaredHTwoIntegral vocabulary. A precise
consumer through the actual IsMaximalSolution bridges should accompany the
source proof. This would close G5, not R43's critical half-order energy (G7),
A05's critical embedding or A04's unconditional continuation.

This note is source-grounded planning. No Lean proof or compilation of the
proposed endpoint theorem is claimed.
