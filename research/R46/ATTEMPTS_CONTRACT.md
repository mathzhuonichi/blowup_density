# Lane 261 — R46 V1 contract registration attempts

## Target and statement fidelity

The registered structure is the complete three-field `REnergyAPI` from
`research/R46/Spec.lean`, renamed only to the registry-conventional
`CompletedDensityAPI`.  A byte comparison from the Proposition 4.6 docstring
through the final field, after that one name substitution, prints
`structure_byte_match: True`.  The contract imports
`Contracts.V1.InsertionFamily`, which supplies the packet and inserted-family
types in the strong-closure field while remaining within the contract import
policy.

The first force-distance summand remains the R46 spelling
`forceSobolevENorm 1 0`.  It is not replaced by R47's
`mixedLebesgueENorm 1 2`; the two registered carriers are not definitionally
equal.  No field, binder, lifespan clause, pressure pin, or shared-family
condition was weakened or omitted.

## Binding route

`Bindings.completedDensity` is the literal record assembly requested for this
lane:

- `completedSobolevDensity` is lane 256's unconditional theorem;
- `completedHomogeneousDensity` is lane 259's
  `completedHomogeneousDensity_of_realization`, instantiated with lane 255's
  `NSFormalization.Section4.I03.compactHomogeneousRealization`;
- `strongTrajectoryClosure` is lane 259's
  `strongTrajectoryClosure_of_realization`, instantiated with the same lane
  255 realization theorem.

All three suppliers already state their conclusions in
`Contracts.V1.Data` vocabulary.  In particular, lane 259 directly constructs
the registered `ClassicalSolutionR` records and registered maximal lifespan,
so this final assembly needs neither a structure conversion nor
`maximalPartial_maximalLifespanR_eq`.  No local definition is restated, hence
there is no additional `rfl` bridge to register.

## Attempts and diagnostics

The first focused build elaborated the contract and binding and the axiom
checker already accepted the witness, but `Tests` rejected a `defProp` linter
warning: a structure with only proposition-valued fields is itself a
proposition.  Declaring `completedDensity` and `checkedCompletedDensity` as
`theorem` rather than `def` removes that warning without changing either type
or proof term.  The next focused build succeeded and reported standard logical
axioms only.

No `sorry`, `admit`, `axiom`, placeholder proposition field, heartbeat
override, or modification of an existing frozen contract/test was needed.
