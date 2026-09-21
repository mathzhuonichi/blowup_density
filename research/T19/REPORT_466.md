# Lane 466 report — T19 U10/U11/U12 projection

## 1. Theorems proved (exact statements)

`NSFormalization.Section3.T19.extendedProductDensity`:

```lean
∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
  ∀ s : ℝ, s < 1 / 2 →
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ g : SpaceTimeField, g ∈ forceClassT →
        ∀ r : ℝ≥0∞, 0 < r →
          ∃ f : SpaceTimeField,
            (a, f) ∈ extendedBreakdownSetT ν T ∧
              forceSobolevENormT 1 s (fun z => f z - g z) < r
```

`NSFormalization.Section3.T19.projectionOntoInitialData`:

```lean
∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
  Prod.fst '' (extendedBreakdownSetT ν T) = initialClassT
```

`NSFormalization.Section3.T19.zeroInitialProjection`:

```lean
∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
  Prod.fst ''
      {p : SpatialField × SpaceTimeField |
        p ∈ extendedBreakdownSetT ν T ∧ p.1 = (fun _ => 0)} =
    {(fun _ => 0 : SpatialField)}
```

U10 directly repackages the witness from `fixedInitialDensity`. U11 and U12
prove set equality by both inclusions; their nonempty fibres use direct proofs
that the zero force and, for U12, the zero initial datum belong to the exact
canonical classes.

## 2. Files

- `formalization/NSFormalization/Section3/T19/Projection.lean`: the three
  theorem implementations.
- `research/T19/probes/projection_closes.lean`: all three canonical field
  result types close by `exact`.
- `research/T19/axioms_u10_u12.lean`: axiom audit for the three theorems.
- `research/T19/ATTEMPTS_U10_U12.md`: route and exact failed probe diagnostic.
- `research/T19/T19_SPLIT.md`: U10/U11/U12 completion status lines.
- `research/T19/REPORT_466.md`: this report.

## 3. Gaps and failed approaches

There are no residual theorem gaps, named inputs, placeholders, or heartbeat
overrides. The only failed run was a probe-only notation-scope omission:

```text
../research/T19/probes/projection_closes.lean:14:21: error: expected token
```

Adding `open scoped ENNReal` to the probe resolved it. No implementation proof
failed. Every theorem's axiom set is exactly
`[propext, Classical.choice, Quot.sound]`.

## 4. Commands and results

- `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T19.DensityEngine`
  — success, 10,658 jobs.
- `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T19.Projection`
  — success, 10,659 jobs.
- `cd verification && lake env lean ../formalization/NSFormalization/Section3/T19/Projection.lean`
  — exit 0, no output.
- `cd verification && lake env lean ../research/T19/probes/projection_closes.lean`
  — exit 0, no output after the recorded scope fix.
- `cd verification && lake env lean ../research/T19/axioms_u10_u12.lean`
  — exit 0; all three declarations printed exactly
  `[propext, Classical.choice, Quot.sound]`.
- `make check` — exit 0; plan, contract policy, policy tests, and work-queue
  checks passed.
