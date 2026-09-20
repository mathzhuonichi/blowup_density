# R45 compact regular-reference rider (lane 254)

## Successful route

- The proof copies the `regularReference` binders and conjunct order from
  `Spec.lean`, specialized to `Y = forceClassCompact`.
- As in lane 249, one call to `insertionLifespanV2_of_data` supplies one R42
  record.  Registered uniqueness identifies its reference velocity with the
  caller's named solution on `[0,T)`.  The record then supplies the inserted
  force, full-horizon classical solution, exact lifespan, expanding history,
  force convergence, and the quantitative energy rate.
- `mainThresholds_energyConvergence` converts that rate into the required
  `Tendsto` statement; `mainThresholds_energy_congr` transports it from the
  record's reference field to the quantified solution `v`.
- Four eventual conditions are intersected at `ε ↓ 0`: the record's valid
  scale window, the requested force ball, the requested energy ball, and
  `ε ≤ min 1 ((T-τ)/4)`.  From the last condition, `ε² ≤ ε` and `τ < T` give
  `τ ≤ T-2ε²`, so the R42 history field covers every requested `t ≤ τ`.
- `forceDifference_compact` plus
  `memForceCompact_add_memForceCompact` keeps the chosen inserted force in
  `F_c`.  Thus the same witnesses satisfy all five Spec conclusions.
- The optional `regularReference_of_memForceR` is derived once from the
  Tendsto-shaped `mainThresholds.regularReferenceApproximation` by the same
  small-scale selection argument.

## Rejected or repaired routes

1. Directly specializing Theorem 4.1's rider cannot prove the compact rider:
   it only says the inserted force lies in `F_R`, not in `F_c`.  The compact
   proof must retain the R42 record so that `forceDifference_compact` remains
   available.
2. Choosing merely `ε ≤ ε₀` is enough for the R42 record, whose fields use
   `Ioc`, but not for Theorem 4.1's family field, which uses `Ioo`.  The
   `F_R` corollary therefore selects `ε ≤ ε₀/2`, yielding the strict
   `ε < ε₀` premise without an endpoint case.
3. Asking `nlinarith` to infer `ε² ≤ ε` implicitly from `0 < ε ≤ 1` was
   brittle.  The final proof first derives it from
   `0 ≤ ε * (1-ε)` and then finishes the cutoff inequality linearly.
4. After substituting the insertion record's `a`, `g`, and `T`, the registered
   uniqueness theorem still needs `MemForceR g`; the compact hypothesis is
   explicitly transported with `memForceR_of_memForceCompact`.

No named supplier hypothesis remains.  In particular, the import graph uses
`Bindings.InsertionFromData` through `Bindings.MainThresholds` and never
imports the incompatible `Bindings.Packet` module.
