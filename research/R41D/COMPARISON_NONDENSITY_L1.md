# Addendum to COMPARISON.md — lane 224

The proposed `RMainAPI.nonDensityZero` field in
`research/section4/STATEMENTS.md` is now proved at q = 1, with explicit
radius `R43.criticalConst * ν`, for every ν,T > 0 and s ≥ 1/2.
`R41.not_breakdownDenseR_zero_L1` gives the exact negation of Data's
`BreakdownDenseR`; the conformance file checks its contract spelling.

This is Theorem 4.1(ii)'s non-density direction. It does not prove either
subcritical `RDensityAPI` field of R41D/Spec.lean, its insertion-witness
requirements, or the q = 2 non-density direction. The existing comparison's
subcritical gap table is unaffected.

R41D/Spec.lean spells thresholds literally, not through an exponent record.
The literal 1/2 agrees with registered `ThresholdAPI.l1` and `energy`.
Order monotonicity is proved for all time exponents and all real orders.

This companion supplies the requested comparison update while respecting
the task's new-files-only rule.
