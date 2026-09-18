# T11/U5 uniqueness package — attempts

## Successful route

- `velocity_unique` converts both `ClassicalSolutionT` witnesses with
  `toFlow` and applies
  `PeriodicLocalLifespan.flow_velocity_agree_on_common_interval` directly.
- For each converted flow, `ClassicalSolutionT.pressure_gauge` states that
  the T10 Haar integral vanishes.  Rewriting Paper 1's `cubeIntegral` with
  `Paper1.integral_torusLift` gives `IsNormalized (toFlow w)`.  The pressure
  component of `PeriodicLocalLifespan.normalized_flows_agree` then proves
  `pressure_unique` pointwise on the exact common half-open interval.
- `horizon_le_lifespan` takes the preceding API `solution` field explicitly
  and uses its selected solution as the witness in the two suprema defining
  `maximalLifespanT`:
  `le_iSup_of_le T (le_iSup_of_le ⟨w⟩ le_rfl)`.  The probe applies this
  bridge to an arbitrary selected `solution` function and therefore closes
  the API field verbatim.
- The non-vacuity probe constructs a genuine nonzero constant-velocity
  `ClassicalSolutionT 1 a 0 1`, proves its datum and force class memberships,
  applies both uniqueness theorems, and places its realized horizon below
  `maximalLifespanT`.
- No instance declaration was introduced.

## Paths tried and exact errors

The implementation module and guarded axiom audit elaborated on their first
direct runs.  The first probe run was made before its already-existing
`CriterionBridge` dependency had been built and reported exactly:

```text
../research/T11/probes/uniqueness_closes.lean:1:0: error: object file '/data_8T/ping/blowup_density/.claude/worktrees/315-T11-U5-uniqueness/formalization/.lake/build/lib/lean/NSFormalization/Section3/T11/CriterionBridge.olean' of module NSFormalization.Section3.T11.CriterionBridge does not exist
```

Running
`lake build NSFormalization.Section3.T11.CriterionBridge` generated the
object; the unchanged probe then passed.

After refining `horizon_le_lifespan` from its realized-horizon core shape to
the API field verbatim (with the preceding `solution` field explicit), one
probe run still imported the previously built `.olean` and therefore saw the
old type:

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

Rebuilding `NSFormalization.Section3.T11.Uniqueness` refreshed the object;
the unchanged probe then passed.

## Residual named input

None.  All three U5 obligations are unconditional once their ordinary
solution arguments (including the selected solution used by the lifespan
field) are supplied.  No peeling hypothesis was introduced.
