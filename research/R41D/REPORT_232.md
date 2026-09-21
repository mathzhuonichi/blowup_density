# Lane 232 — combined Theorem 4.1(ii) non-density

## 1. Theorem proved

For real `q` with `q = 1 ∨ q = 2`, positive `ν,T`, and every
`s ≥ thresholds.exponent q 0`, `nonDensityZero_of_q` gives a positive radius
whose `ENNReal.ofReal` lower-bounds the `L^q_t H^s_x` norm of every force in
the zero-datum breakdown set.  The witness is explicitly
`R43.criticalConst * ν` in the `q = 1` case and `R44.radius ν T` in the
`q = 2` case.  `not_breakdownDenseR_zero_of_q` proves the corresponding
negation of `BreakdownDenseR`, which is Theorem 4.1(ii)'s only-if half.

The skeleton's `q : ℝ` is retained and is passed to the implementation norm
as `ENNReal.ofReal q`.  Under the required case split this is exactly the
literal norm exponent `1` or `2`, matching `R41D/Spec.lean`; changing the API
binder itself to `ℝ≥0∞` would not match the real-valued threshold exponent.

## 2. What is in Lean

`formalization/NSFormalization/Section4/R41/NonDensity.lean` adds the
ThresholdAPI-shaped local record `RMainThresholds`, its canonical
`Paper3.forceExponent` value, the two combined theorems, and
`RMainNonDensity`.  The latter mirrors the future assembly order
`ν, T, hν, hT, q, hq, thresholds` and contains only the proved
`nonDensityZero` field.  Two `⟨…⟩` examples instantiate it at `ν = T = 1`
for both exponents, and two further examples exclude density there.

`research/R41D/axioms_nondensity.lean` converts any frozen
`Contracts.V1.ThresholdAPI` to the local record, proves the canonical local
and registered exponent projections equal by `rfl`, bridges the local
breakdown vocabulary to `Contracts.V1.Data`, and restates both conclusions in
that vocabulary.  All fourteen audited named declarations print exactly
`[propext, Classical.choice, Quot.sound]`.  `ATTEMPTS_NONDENSITY.md` records
the cast decision and rejected alternatives, and `COMPARISON.md` now marks
the combined field proved.

## 3. Remaining gaps

None remain for the non-density clause for `q ∈ {1,2}`.  This lane does not
claim or package `densityFixedInitial`, `densityZero`, or
`regularReferenceRider`, and it does not register a full `RMainAPI`.  Those
subcritical density and insertion assertions remain separate work.

## 4. Commands and results

All Lean commands ran after `. scripts/lean-env.sh`; Lake commands ran from
`verification/` with `LEAN_NUM_THREADS=6` where requested.

- `lake build NSFormalization.Section4.R41.NonDensity`: exit 0.  The new
  module emits no warning; Lake replays pre-existing warnings from dependency
  modules, so aggregate output is not literally empty.
- `lake env lean ../formalization/NSFormalization/Section4/R41/NonDensity.lean`:
  exit 0 with zero output.
- `lake env lean ../research/R41D/axioms_nondensity.lean`: exit 0; all fourteen
  reports list exactly the standard three axioms and both registered
  non-vacuity examples pass.
- `make check`: exit 0; all 13 policy tests and all 30 work-item checks pass.
- `git diff --check`: exit 0.

Committed on `erenup/232-R41-nondensity-both`; no push, merge, or rebase.
