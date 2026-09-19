# Lane 452 report — T20 U5 `constantTransportCommutesLambda`

## 1. Theorem proved (exact statement)

`formalization/NSFormalization/Section3/T20/TransportLambda.lean` proves the
canonical `CriticalRegularityTAPI` field verbatim:

```lean
theorem constantTransportCommutesLambda :
    ∀ (m : Space) (v Lv : SpatialField), SmoothPeriodicT v →
      IsPeriodicLambda v Lv →
        IsPeriodicLambda (constantTransportSpatialT m v)
          (constantTransportSpatialT m Lv)
```

Thus the conclusion is the concrete `IsPeriodicLambda` graph for the two
transported physical fields, not an equality of fields.  The proof expands
constant transport into coordinate derivatives to preserve smooth periodicity,
then commutes its Fourier symbol with the scalar Lambda symbol coefficientwise.

## 2. Files delivered

- `formalization/NSFormalization/Section3/T20/TransportLambda.lean` — U5 proof.
- `research/T20/probes/transport_lambda_closes.lean` — exact field-type match
  against both `CriticalRegularityTAPI.constantTransportCommutesLambda` and the
  proved theorem, plus the nonzero witness
  `meanZeroPartT (x ↦ cos(2π x₀) • e₀)` with `Lv` from `lambda_exists`.
- `research/T20/axioms_u5.lean` — transitive axiom audit.
- `research/T20/ATTEMPTS_U5.md` — successful route and resolved failures.
- `research/T20/T20_SPLIT.md` — U5 marked DONE.
- `research/T20/REPORT_452.md` — this report.

## 3. Gaps and residual errors

None.  There is no named input, placeholder, residual theorem, or unresolved
Lean error.  Fourier injectivity is not a missing step: the canonical target's
`IsPeriodicLambda` predicate already asks directly for the coefficientwise
identity.  The axiom audit prints exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The two transient elaboration/scope errors encountered during development and
their exact messages are recorded in `research/T20/ATTEMPTS_U5.md`; both are
resolved in the delivered files.

## 4. Commands and results

Run with `. scripts/lean-env.sh`; every `lake` invocation was made from
`verification/` with the requested thread cap on builds.

- `LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T20.CriticalEnergy NSFormalization.Section3.T20.ConstantTransport`
  — dependency closure built successfully.
- `LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T20.TransportLambda`
  — success, 0 errors.
- `lake env lean ../formalization/NSFormalization/Section3/T20/TransportLambda.lean`
  — success, 0 output.
- `lake env lean ../research/T20/probes/transport_lambda_closes.lean`
  — success, 0 output.
- `lake env lean ../research/T20/axioms_u5.lean`
  — success; theorem depends exactly on `propext`, `Classical.choice`, and
  `Quot.sound`.
- `make check`
  — success; formalization-plan, contract-policy, policy tests, and work-queue
  checks all passed.
