# Lane 249 — contract binding attempts

## Accepted route

Copied the complete `RMainAPI` structure body from `Spec.lean`, including field
order, binders, hypotheses, conclusions and documentation; only the structure
name becomes `MainThresholdsAPI`. Contract imports only `Contracts.V1.Data`.
The Tests file restates each of the four field types independently.

Lane 235 binds fixed-data density and the reverse zero-data implication.
Lane 232 binds non-density after splitting the ENNReal exponent into 1 and 2,
instantiating its real exponent with the corresponding numeral, and transporting
`breakdownSetR` through `maximalPartial_maximalLifespanR_eq`. Force class and
force norm have explicit `rfl` bridges. Threshold values are arithmetic.

For the rider, the named solution supplies `RegularThrough`. Call lane 233's
`insertionLifespanV2_of_data` exactly once. Substitute its three data equalities
before using the reference and inserted solutions; this avoids unnecessary
casts between dependent solution types. Registered uniqueness identifies the
record's reference with the named reference on `[0,T)`. The supplied history
window lies strictly below T since ε > 0. All forces, velocities, solutions,
lifespans and both limits use this single record.

The registered `energyRate` is already a bound in `Data.energyENorm`; its RHS
is continuous at zero and vanishes there, by positivity of the two real powers.
Use the order-topology squeeze theorem for ENNReal. The energy congruence lemma
uses equality of whole spatial slices on `(0,T)`, which also identifies their
spatial derivatives; no equality outside the solution interval is assumed.

## Rejected implementation attempts

- `squeeze_zero'` is specialized to real-valued functions (`failed to synthesize
  IsBotZeroClass ℝ` under the attempted inference). Replaced it with
  `tendsto_of_tendsto_of_tendsto_of_le_of_le'` in ENNReal.
- Transporting solution records with `simpa only [hLa,hLg,hLT]` left projection
  and cast mismatches (`U.velocity` versus `U'.velocity`, and `.g` versus the
  nested correction projection). Substitute the three original data variables
  once instead; the single chosen record and all field types then agree.
- An unannotated `Ioc_mem_nhdsGT ...` was viewed as set membership in a filter,
  so `.mono` resolved against `Exists`. Annotate the eventual statement first.
- Selective namespace opening `open NSFormalization.Section4 (R41)` treats R41
  as a declaration, not a namespace. Use the enclosing namespace opening.

## Fidelity and missing input file

No field is omitted or weakened; a partial API is unnecessary. The requested
`research/R41/RECONCILIATION.md` is absent from this checkout (also absent from
`rg --files research`). The existing reconciled `Spec.lean` and its detailed
`COMPARISON.md` binding plan are the statement authority used here. No replacement
reconciliation or new statement decision was invented.
