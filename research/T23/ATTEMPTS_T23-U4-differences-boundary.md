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
