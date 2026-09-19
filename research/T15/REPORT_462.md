# Lane 462 — T15 U14b

## 1. Theorem and exact statement

Completed `forceConvergence_two` and the full canonical `forceConvergence`.
Both use only the raw smoothness/support hypotheses and `PlacementData`:

```lean
theorem forceConvergence_two
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hf : ContDiff ℝ ∞ f)
    (hc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u p f K) :
    ∀ s : ℝ, s < criticalOrder ((2 : ℝ≥0∞).toReal) →
      Tendsto (fun ε : ℝ ↦ forceSobolevENormT 2 s
        (periodizedScaledForce f place.x₀ place.T ε)) (𝓝[>] 0) (𝓝 0)

theorem forceConvergence
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hf : ContDiff ℝ ∞ f)
    (hc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u p f K) :
    ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) → ∀ s : ℝ, s < criticalOrder q.toReal →
      Tendsto (fun ε : ℝ ↦ forceSobolevENormT q s
        (periodizedScaledForce f place.x₀ place.T ε)) (𝓝[>] 0) (𝓝 0)
```

The proof establishes sharp `Summable (fun k ↦ W k ^ r)` for every
`r < -3/2` using three one-dimensional Bessel-weight series. Fourier
coefficient control gives `‖A‖ ≤ sqrt(3 * Σ W^r) * ‖z‖₁`. The existing
single-copy mixed scaling at spatial exponent 1 therefore yields an `ε`
bound in `L²_t H^r_x`. Genuine datum interpolation and time Hölder combine
this with the order-zero Parseval scaling `ε^(-1/2)`, giving
`ε^(1-3θ/2)`. For the remaining orders choose
`r = (3*s - 3/2)/2`, `θ = 1-s/r`; then `3*s < r < -3/2` and the exponent
is positive. The final theorem combines this result with lane 458's `q=1`
theorem. No existing Lean module was changed.

## 2. Files

- `formalization/NSFormalization/Section3/T15/ConvergenceTwo.lean`: 17 proved
  declarations, including both complete convergence theorems.
- `research/T15/probes/convergence_two_closes.lean`: the literal canonical
  field closed by `exact`, plus an explicit nonzero smooth compact bump
  packet and placement satisfying the full two-exponent conclusion.
- `research/T15/axioms_u14b.lean`: all 17 declarations audited.
- `research/T15/ATTEMPTS_U14b.md`: failed elaboration attempts and exact
  diagnostics, with their resolutions.
- `research/T15/T15_SPLIT.md`: U14b completion status.
- `research/T15/REPORT_462.md`: this report.

## 3. Gaps and errors

No remaining mathematical gap or residual strip. No named inputs,
placeholders, admission, extra axioms, or heartbeat overrides were added.
All 17 module declarations print exactly
`[propext, Classical.choice, Quot.sound]`.

The development errors are resolved and recorded in `ATTEMPTS_U14b.md`.
Representative exact errors were:

```text
error(lean.unknownIdentifier): Unknown constant `ENNReal.mul_rpow`
error(lean.synthInstanceFailed): failed to synthesize instance of type class
  SeparatelyContinuousMul ℝ≥0∞
```

They were fixed using `ENNReal.mul_rpow_of_nonneg` and the finite-factor
`ENNReal.Tendsto.mul_const`/`const_mul` theorems.

## 4. Commands and results

With `. scripts/lean-env.sh`, the requested Lake commands ran from
`verification/` with `LEAN_NUM_THREADS=6`:

```text
lake build NSFormalization.Section3.T15.Convergence
  exit 0; Build completed successfully (10024 jobs).
lake build NSFormalization.Section3.T15.ConvergenceTwo
  exit 0; Build completed successfully (10040 jobs).
lake env lean ../formalization/NSFormalization/Section3/T15/ConvergenceTwo.lean
  exit 0; no output.
lake env lean ../research/T15/probes/convergence_two_closes.lean
  exit 0; no output.
lake env lean ../research/T15/axioms_u14b.lean
  exit 0; all 17 declarations print exactly the three standard axioms.
make check
  exit 0; architecture, contract policy (13 tests), and work queue passed.
make test
  exit 0; registered contract tests passed.
LEAN_NUM_THREADS=6 make test-mutations
  exit 0; refactor accepted; admission, extra-axiom, and weakened-hypothesis
  mutations rejected as required.
```
