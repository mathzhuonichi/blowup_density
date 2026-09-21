# Lane 315 report — T11/U5 uniqueness package

## 1. Theorems with exact statements

```lean
theorem velocity_unique : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionT ν a f T₁)
          (u₂ : ClassicalSolutionT ν a f T₂),
          ∀ t ∈ Ico (0 : ℝ) (min T₁ T₂), ∀ x : Space,
            u₁.velocity (t, x) = u₂.velocity (t, x)
```

```lean
theorem pressure_unique : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionT ν a f T₁)
          (u₂ : ClassicalSolutionT ν a f T₂),
          ∀ t ∈ Ico (0 : ℝ) (min T₁ T₂), ∀ x : Space,
            u₁.pressure (t, x) = u₂.pressure (t, x)
```

```lean
theorem horizon_le_lifespan
    {horizon : ℝ → SpatialField → SpaceTimeField → ℝ}
    (solution : ∀ (ν : ℝ), 0 < ν →
      ∀ (a : SpatialField), a ∈ initialClassT →
        ∀ (f : SpaceTimeField), f ∈ forceClassT →
          ClassicalSolutionT ν a f (horizon ν a f)) :
    ∀ (ν : ℝ), 0 < ν →
      ∀ (a : SpatialField), a ∈ initialClassT →
        ∀ (f : SpaceTimeField), f ∈ forceClassT →
          ENNReal.ofReal (horizon ν a f) ≤ maximalLifespanT ν a f
```

The conclusion of the third theorem is the API field verbatim; its preceding
`solution` field is an explicit argument.  Velocity uniqueness comes from
`flow_velocity_agree_on_common_interval`; pressure uniqueness converts the
T10 Haar gauge to Paper 1 normalization with `integral_torusLift` and applies
`normalized_flows_agree`.  The lifespan proof is the defining double-supremum
witness and performs no flow conversion.

## 2. Files

- `formalization/NSFormalization/Section3/T11/Uniqueness.lean` — the three U5
  theorems.
- `research/T11/probes/uniqueness_closes.lean` — verbatim field closure checks
  and a nonzero constant-flow non-vacuity witness.
- `research/T11/axioms_uniqueness.lean` — guarded checks requiring exactly
  `[propext, Classical.choice, Quot.sound]` for every exported declaration.
- `research/T11/ATTEMPTS_UNIQUENESS.md` — proof routes, exact transient errors,
  and the no-named-input record.
- `research/T11/T11_SPLIT.md` — appended U5 completion status.

## 3. Gaps with error text

No proof gap and no residual named input remain.  No instance declaration was
added.  The two transient failures were build-cache issues, not proof
obligations:

```text
../research/T11/probes/uniqueness_closes.lean:1:0: error: object file '/data_8T/ping/blowup_density/.claude/worktrees/315-T11-U5-uniqueness/formalization/.lake/build/lib/lean/NSFormalization/Section3/T11/CriterionBridge.olean' of module NSFormalization.Section3.T11.CriterionBridge does not exist
```

and, after a source-only direct check left the old `Uniqueness.olean` in
place:

```text
../research/T11/probes/uniqueness_closes.lean:45:28: error: Application type mismatch: The argument
  solution
has type
  (ν : ℝ) →
    0 < ν →
      (a : SpatialField) →
        a ∈ initialClassT → (f : SpaceTimeField) → f ∈ forceClassT → ClassicalSolutionT ν a f (horizon ν a f)
but is expected to have type
  ClassicalSolutionT ?m.24 ?m.26 ?m.27 ?m.25
in the application
  horizon_le_lifespan solution
```

Building the respective existing targets refreshed both objects; the
unchanged probe passed afterward.

## 4. Commands and results

- `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.Uniqueness`
  — passed, 0 errors.
- `cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T11/Uniqueness.lean`
  — passed, no diagnostics.
- `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T11/probes/uniqueness_closes.lean`
  — passed, no diagnostics; all exact targets and the non-vacuity witness
  elaborate.
- `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T11/axioms_uniqueness.lean`
  — passed; all three guarded declarations print exactly the standard three
  axioms.
- `make check` from the worktree root — passed.
