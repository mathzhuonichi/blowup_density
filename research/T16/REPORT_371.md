# T16 lane 371 report

What is registered: `T02.local_potential` V1, the reconciled form of `lem:potential`, including the four helper definitions, seven-field `CutoffData`, and 26-field `LocalPotentialAPI`.

Lean now contains `Contracts/V1/LocalPotential.lean`, `Bindings/LocalPotential.lean`, and `Tests/LocalPotential.lean`. The binding supplies four rfl helper bridges, fieldwise data/API conversion, round trips, and the transported assembly theorem. The test includes the axiom audit and zero non-vacuity witness.

No correction norm bound is asserted; that remains T17. The local smoothness and periodic correction clauses are exactly those in the reconciled specification.

Validated with `lake build` for the contract, canonical assembly, and binding, followed by the local test and axiom check. Registry and T16 ledger entries were rendered; full repository gates remain to be run before integration.
