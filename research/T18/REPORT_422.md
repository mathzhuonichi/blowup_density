# Lane 422 report — T18 U1 insertion data

## 1. Theorems and exact statements

`NSFormalization.Section3.T18.InsertionData` replaces the contract-only packet
parameter by the raw fields
`packetVelocity`, `packetPressure`, `packetForce`, `carrier`, `energyBound`,
and `dissipationBound`, then bundles the canonical `place`, `scaling`,
`reference`, `D`, and `correction` records together with `hδ`, `hg`, and `ha`.

For `data : InsertionData`, the new data are exactly:

```lean
def velocity (data : InsertionData) (ε : ℝ) (z : SpaceTime) : Space :=
  data.reference.velocity z + data.D.correction ε z +
    periodizedScaledVelocity data.packetVelocity data.place.x₀ data.place.T ε z

def pressure (data : InsertionData) (ε : ℝ) : SpaceTimeScalar :=
  normalizePressureT (fun z ↦ data.reference.pressure z +
    periodizedScaledPressure data.packetPressure data.place.x₀ data.place.T ε z)

def force (data : InsertionData) (ε : ℝ) (z : SpaceTime) : Space :=
  data.g z + correctionForce data.ν data.reference.velocity data.D ε z +
    periodizedScaledForce data.packetForce data.place.x₀ data.place.T ε z

def ε₀ (data : InsertionData) : ℝ := min data.place.ε₀ data.D.ε₀
```

The exact theorem statements are:

```lean
theorem velocity_formula (data : InsertionData) : ∀ ε : ℝ, ∀ z : SpaceTime,
  velocity data ε z = data.reference.velocity z + data.D.correction ε z +
    periodizedScaledVelocity data.packetVelocity data.place.x₀ data.place.T ε z

theorem pressure_formula (data : InsertionData) : ∀ ε : ℝ,
  pressure data ε = normalizePressureT
    (fun z ↦ data.reference.pressure z +
      periodizedScaledPressure data.packetPressure data.place.x₀ data.place.T ε z)

theorem force_formula (data : InsertionData) : ∀ ε : ℝ, ∀ z : SpaceTime,
  force data ε z = data.g z +
    correctionForce data.ν data.reference.velocity data.D ε z +
    periodizedScaledForce data.packetForce data.place.x₀ data.place.T ε z

theorem eps_pos (data : InsertionData) : 0 < ε₀ data
theorem eps_le_scaling (data : InsertionData) : ε₀ data ≤ data.place.ε₀
theorem eps_le_cutoff (data : InsertionData) : ε₀ data ≤ data.D.ε₀
theorem delta_pos (data : InsertionData) : 0 < data.δ
theorem reference_force_mem (data : InsertionData) : data.g ∈ forceClassT
theorem initial_mem (data : InsertionData) : data.a ∈ initialClassT
```

The three formulas are definitional. `eps_pos` uses
`data.place.eps_pos` and `data.correction.potential.eps_pos`; the latter is the
canonical source of `0 < data.D.ε₀`, because raw `CutoffData` has no positivity
field.

## 2. Files

- `formalization/NSFormalization/Section3/T18/Insertion.lean`: canonical U1
  bundle, inserted triple, three formula theorems, common threshold, and the
  five elementary hypothesis/bound theorems.
- `research/T18/probes/insertion_closes.lean`: Spec-form 17-field placement and
  7-field cutoff restatements, fieldwise adapters, contract T11 reference
  conversion, all eleven U1 fields, and a conditional `Nonempty` example.
- `research/T18/axioms_u1.lean`: axiom audit for every canonical U1 declaration.
- `research/T18/ATTEMPTS_U1.md`: substitution table, elaboration notes, and
  concrete-witness search.
- `research/T18/T18_SPLIT.md`: U1 completion status.
- `research/T18/REPORT_422.md`: this report.

## 3. Gaps and error text

There is no unresolved proof, statement, elaboration, or gate error.

There is no fully concrete `InsertionData` witness in the current tree. The
required `grep -rn` search found that
`research/T15/probes/placement_closes.lean` is explicitly not a full
`PlacementData`: its displayed `T = ε₀ = 1` fails `eps_time` at `ε = 1`.
T11 does provide concrete classical reference solutions, but the remaining
missing witnesses are exactly:

1. a full 17-field `PlacementData` together with a full 21-field `ScalingAPI`
   (T15 U15), and
2. a full 45-field `CorrectionAPI` (T17 assembly).

The resolved compiler messages and their fixes are recorded verbatim in
`ATTEMPTS_U1.md`; none remains in the final files.

## 4. Commands and results

All Lake commands were run from `verification/` after sourcing
`scripts/lean-env.sh`; builds used `LEAN_NUM_THREADS=6`.

| Command | Result |
|---|---|
| `lake build NSFormalization.Section3.T18.Insertion` | pass, 0 errors |
| `lake env lean ../formalization/NSFormalization/Section3/T18/Insertion.lean` | pass, 0 output |
| `lake env lean ../research/T18/probes/insertion_closes.lean` | pass, 0 output |
| `lake env lean ../research/T18/axioms_u1.lean` | pass; all 15 declarations print exactly `[propext, Classical.choice, Quot.sound]` |
| `make check` | pass: plan check, contract/import policy tests, and work queue |

`git diff --check` also passes with no output.
`make check` retained the repository-wide pre-existing
`source_hashes_match=false` and copied-source admission inventory; its exit
status was 0 and both the 13 policy tests and 45-item work-queue check passed.
