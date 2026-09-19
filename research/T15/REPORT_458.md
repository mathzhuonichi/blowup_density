# Lane 458 report — T15 U14 force convergence

## 1. Theorems and exact statements

This lane is an honest partial of the canonical `ScalingAPI.forceConvergence`
field. It proves the complete literal `q = 1` specialization over exactly the
raw packet hypotheses used:

```lean
theorem forceConvergence_one
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hf : ContDiff ℝ ∞ f)
    (hc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u p f K) :
    ∀ s : ℝ, s < criticalOrder ((1 : ℝ≥0∞).toReal) →
      Tendsto
        (fun ε : ℝ ↦ forceSobolevENormT 1 s
          (periodizedScaledForce f place.x₀ place.T ε))
        (nhdsWithin 0 (Ioi 0)) (nhds 0)
```

For `0 ≤ s < 1/2`, `forceConvergence_one_nonnegative` squeezes the packet norm
by U13's `packetSobolevBound`; both real powers tend to zero, and
`Ioc_mem_nhdsGT place.eps_pos` supplies the eventual admissible scale. For
`s < 0`, `forceSobolevENormT_mono_order` maps every datum path through the
bounded Fourier reweighting `persistenceDown`, then compares with the proved
order-zero limit. The auxiliary `persistenceDown_norm_le_one` exposes the
existing T11 contraction theorem without identifying phantom-indexed datum
types.

Every declaration in the new formalization module audits to exactly:

```text
[propext, Classical.choice, Quot.sound]
```

## 2. Files

- `formalization/NSFormalization/Section3/T15/Convergence.lean`: four proved
  declarations covering order monotonicity and the full `q = 1` result.
- `research/T15/probes/convergence_closes.lean`: literal raw-clause conformance
  by `exact`, plus a genuinely nonzero compact bump force and placement.
- `research/T15/axioms_u14.lean`: axiom audit of every module declaration.
- `research/T15/ATTEMPTS_U14.md`: failed approaches, exact errors, and residual.
- `research/T15/T15_SPLIT.md`: U14 status correction.
- `research/T15/REPORT_458.md`: this report.

## 3. Gap and exact error

The full canonical theorem additionally requires `q = 2` for all
`s < -1/2`. The requested order-zero route cannot prove it because the
registered exponent is

```text
alphaT 2 2 = -3 + 3/2 + 1 = -1/2,
```

so the order-zero norm scales like `ε ^ (-1/2)` rather than tending to zero.
Lean rejects the claimed positivity with:

```text
/tmp/q2_arithmetic_458.lean:3:28: error: unsolved goals
⊢ False
```

The exact remaining statement is:

```lean
∀ s : ℝ, s < criticalOrder ((2 : ℝ≥0∞).toReal) →
  Tendsto
    (fun ε : ℝ ↦ forceSobolevENormT 2 s
      (periodizedScaledForce f place.x₀ place.T ε))
    (𝓝[>] 0) (𝓝 0)
```

The tree has the whole-space negative-order result in
`Source/CompactForceConvergence.lean`, but no torus periodization bridge that
preserves it. Attempting `exact forceConvergence_one hf hc place` at the full
field gives the type mismatch recorded verbatim in `ATTEMPTS_U14.md`. No
assumption, named input, placeholder, or repackaged goal was added.

## 4. Commands and results

The final verification results are recorded here after running the gates:

```text
LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T15.Convergence
  Build completed successfully (10024 jobs).

LEAN_NUM_THREADS=6 lake env lean \
  ../formalization/NSFormalization/Section3/T15/Convergence.lean
  exit 0; no output

LEAN_NUM_THREADS=6 lake env lean \
  ../research/T15/probes/convergence_closes.lean
  exit 0; no output

LEAN_NUM_THREADS=6 lake env lean ../research/T15/axioms_u14.lean
  exit 0; all four declarations print exactly
  [propext, Classical.choice, Quot.sound]

make check
  exit 0; architecture, contract-policy, and work-queue checks passed
```
