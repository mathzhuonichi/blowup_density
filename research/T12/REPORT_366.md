# Lane 366-T12-U1 report

The API bridge and the supported-in-cube scalar/vector `L^p` transfer are proved.
The periodic Haar/cube theorem is reduced for finite nonzero `p` to one explicit
lintegral identity, matching the fundamental-domain argument in T13.

Lean now contains `HaarCube.lean`, with the p=3 and p=6 API probes.

The remaining gap is the general measurable ENNReal density identity (including
the endpoint cases); no placeholder or axiom was added.

Validation: module source and probe checked with `lake env lean`; full build and
`make check` remain to be run by the integrator after this partial lane result.
