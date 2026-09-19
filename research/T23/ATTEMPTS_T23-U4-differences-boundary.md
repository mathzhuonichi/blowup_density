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
