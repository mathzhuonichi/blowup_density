# T23 U4 attempts — localized differences and boundary retention

This file records failed proof approaches with their exact Lean diagnostics.

## A1. Namespaced neighborhood constant

The first slice-support helper used `Filter.nhds`.  Lean 4.34.0-rc2 reported:

```text
../formalization/NSFormalization/Section3/T23/Differences.lean:112:20: error(lean.unknownIdentifier): Unknown constant `Filter.nhds`
../formalization/NSFormalization/Section3/T23/Differences.lean:115:7: error(lean.unknownIdentifier): Unknown constant `Filter.nhds`
../formalization/NSFormalization/Section3/T23/Differences.lean:115:23: error(lean.unknownIdentifier): Unknown constant `Filter.nhds`
```

Resolution: open `Filter` and use the standard neighborhood notation `𝓝`, as
in the already checked T18 support proof.

## A2. Ambiguous function argument in support evaluation

The first collar proof left the slice function implicit in
`image_eq_zero_of_notMem_tsupport`. Lean inferred the point value as the
function and reported:

```text
../formalization/NSFormalization/Section3/T23/Differences.lean:224:57: error: Application type mismatch: The argument
  hxnot
has type
  x ∉ tsupport fun y => velocity ε (t, y) - v (t, y)
but is expected to have type
  v (t, x) ∉ tsupport (HSub.hSub (velocity ε (t, x)))
in the application
  image_eq_zero_of_notMem_tsupport hxnot
```

Resolution: supply `(f := fun y : Space => velocity ε (t,y) - v (t,y))`
explicitly.

## A3. Lambda subtraction did not rewrite as pointwise subtraction

The first divergence proof applied `spatialDerivative_sub_at`, whose conclusion
uses the pointwise function subtraction notation, directly to the API's
explicit lambda. Lean left the divergence derivative unreduced:

```text
../formalization/NSFormalization/Section3/T23/Differences.lean:288:2: error: Type mismatch
  sub_eq_zero.mpr (Eq.trans (hincompressible ε hε t ht x hx) (Eq.symm (reference.divergence t htref x hx)))
has type
  spatialDivergence (velocity ε) t x - spatialDivergence reference.velocity t x = 0
but is expected to have type
  ∑ x_1, ((spatialDerivative (fun z => velocity ε z - reference.velocity z) t x) (coordinateVector x_1)).ofLp x_1 = 0
```

Lean also warned that `hd`, `sub_apply`, `PiLp.sub_apply`, and
`Finset.sum_sub_distrib` were unused. Resolution: first `change` the explicit
lambda target to `spatialDivergence (velocity ε - reference.velocity) ... = 0`;
then the local derivative equality rewrites exactly.

## A4. Probe hypotheses left as section variables

The first exact-field probe left the two U3 facts `hvelocity_smooth` and
`hincompressible` as surrounding section variables. Lean accepted the example
but diagnosed the generated declaration:

```text
../research/T23/probes/T23-U4-differences-boundary_closes.lean:63:0: warning: declaration uses `sorry`
```

Adding explicit named parameters to the theorem application did not remove the
warning. Resolution: bind both hypotheses explicitly on that `example`; the
same `by exact velocityDifference_divFree ...` then elaborates with zero
output and no hidden synthetic placeholder.
