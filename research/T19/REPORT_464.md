# Lane 464 report — T19 U7/U8/U9 density engine

## 1. Theorems proved (exact statements)

`NSFormalization.Section3.T19.fixedInitialDensity`:

```lean
∀ a : SpatialField, a ∈ initialClassT →
  ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
    ∀ s : ℝ, s < 1 / 2 →
      RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)
```

`NSFormalization.Section3.T19.regularReferenceSingular`:

```lean
∀ a : SpatialField, a ∈ initialClassT →
  ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
    ∀ g : SpaceTimeField, g ∈ forceClassT → RegularThroughT ν a g T →
      ∀ s : ℝ, s < 1 / 2 → ∀ r : ℝ≥0∞, 0 < r →
        ∃ f ∈ forceClassT,
          forceSobolevENormT 1 s (fun z => f z - g z) < r ∧
            maximalLifespanT ν a f = ENNReal.ofReal T
```

`NSFormalization.Section3.T19.mixedDensity`:

```lean
∀ a : SpatialField, a ∈ initialClassT →
  ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
    ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
      3 < 3 / p.toReal + 2 / q.toReal →
        RelativelyDenseMixedT q p forceClassT (breakdownSetT ν a T)
```

The fixed-initial and mixed statements split on
`maximalLifespanT ν a g ≤ ENNReal.ofReal T`.  The already-singular branch
uses the U6 zero-norm representatives.  In the other branch, the defining
double supremum for `maximalLifespanT` produces a realized longer horizon
and hence `RegularThroughT`.  U7/U8 then use U0's
`exists_force_close`; U9 uses U0's mixed bound together with U2's two
positive exponents.

## 2. Files

- `formalization/NSFormalization/Section3/T19/DensityEngine.lean`: the three
  theorem implementations.
- `research/T19/probes/density_engine_closes.lean`: all three canonical
  field result types close by `exact`.
- `research/T19/axioms_u7_u9.lean`: axiom audit for the three theorems.
- `research/T19/ATTEMPTS_U7_U9.md`: complete unsuccessful-attempt log with
  verbatim Lean diagnostics.
- `research/T19/T19_SPLIT.md`: U7/U8/U9 completion status lines.
- `research/T19/REPORT_464.md`: this report.

## 3. Gaps and failed approaches

There are no residual theorem gaps and no named inputs or placeholders.
The failed elaboration attempts were mechanical:

```text
error: NSFormalization/Section3/T19/DensityEngine.lean:100:11: unexpected token '>'; expected ':' or term
error: NSFormalization/Section3/T19/DensityEngine.lean:86:56: Unknown identifier `𝒩`
```

```text
error: NSFormalization/Section3/T19/DensityEngine.lean:86:56: expected token
error: NSFormalization/Section3/T19/DensityEngine.lean:86:17: type expected, got
  (Tendsto (fun ε => ε ^ alphaT p q) ?m.200 : Filter ℝ → Prop)
```

```text
error: NSFormalization/Section3/T19/DensityEngine.lean:74:4: Type mismatch: After simplification, term
  hr
 has type
  0 < r
but is expected to have type
  (mixedLebesgueENormT q p fun z => 0) < r
```

The initial probe also used record projections as types and produced
`error: type expected, got` at lines 5, 8, and 11.  The full exact output
and each resolution are in `ATTEMPTS_U7_U9.md`.

## 4. Commands and results

- `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T19.Threading NSFormalization.Section3.T19.Density`
  — success, 10,657 jobs.
- `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T19.DensityEngine`
  — success, 10,658 jobs.
- `cd verification && lake env lean ../formalization/NSFormalization/Section3/T19/DensityEngine.lean`
  — exit 0, no output.
- `cd verification && lake env lean ../research/T19/probes/density_engine_closes.lean`
  — exit 0, no output.
- `cd verification && lake env lean ../research/T19/axioms_u7_u9.lean`
  — exit 0; every declaration printed exactly
  `[propext, Classical.choice, Quot.sound]`.
- `make check` — exit 0; plan, contract policy, policy tests, and work-queue
  checks passed.
