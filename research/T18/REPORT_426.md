# Lane 426 report — T18 U2/U3/U4

## 1. Theorems and exact statements

All nine fields are proved in `NSFormalization.Section3.T18`. The parameters
are the U1 `InsertionData` projections, with no additional hypotheses.

```lean
theorem force_mem (data : InsertionData) : ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
    force data ε ∈ forceClassT

theorem forceDifference_mem (data : InsertionData) : ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
    (fun z ↦ force data ε z - data.g z) ∈ forceClassT

theorem velocity_smooth (data : InsertionData) : ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
    ContDiffOn ℝ ∞ (velocity data ε) (Ico (0 : ℝ) data.place.T ×ˢ (univ : Set Space))

theorem pressure_smooth (data : InsertionData) : ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
    ContDiffOn ℝ ∞ (pressure data ε) (Ico (0 : ℝ) data.place.T ×ˢ (univ : Set Space))

theorem initial (data : InsertionData) : ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
    ∀ x : Space, velocity data ε (0, x) = data.a x

theorem history (data : InsertionData) : ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
    ∀ t : ℝ, 0 ≤ t → t ≤ data.place.T - 2 * ε ^ 2 → ∀ x : Space,
      velocity data ε (t, x) = data.reference.velocity (t, x)

theorem velocity_periodic (data : InsertionData) : ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
    IsPeriodicOn (Ico (0 : ℝ) data.place.T) (velocity data ε)

theorem incompressible (data : InsertionData) : ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
    ∀ t ∈ Ico (0 : ℝ) data.place.T, ∀ x : Space,
      spatialDivergence (velocity data ε) t x = 0

theorem velocityDifference_divFree (data : InsertionData) : ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
    ∀ t ∈ Ico (0 : ℝ) data.place.T, ∀ x : Space,
      spatialDivergence (fun z ↦ velocity data ε z - data.reference.velocity z) t x = 0
```

The proof uses compact support unions, summand smoothness/periodicity,
additivity of pressure normalization on integrable slices, the explicit
packet zero extension, and spatial divergence additivity. Seven auxiliary
lemmas plus the spatial slicing lemma make 17 canonical declarations total;
all have exactly `[propext, Classical.choice, Quot.sound]` as axioms.

## 2. Files

- `formalization/NSFormalization/Section3/T18/ForceClass.lean`: two U2 fields,
  range transport, force-class addition, and correction-force membership.
- `formalization/NSFormalization/Section3/T18/Kinematics.lean`: all five U3
  fields, reference time inclusion, and two quiet-summand lemmas.
- `formalization/NSFormalization/Section3/T18/Divergence.lean`: both U4 fields
  and spatial slice differentiability including time zero.
- `research/T18/probes/u2_u4_closes.lean`: standalone copy of the U1 fieldwise
  adapters and its constructor, followed by the nine exact Spec-form fields
  and their canonical discharge. Registered contract vocabulary is used.
- `research/T18/axioms_u2_u4.lean`: all 17 canonical declarations audited.
- `research/T18/ATTEMPTS_U2_U4.md`: successful routes and resolved errors.
- `research/T18/T18_SPLIT.md`: U2/U3/U4 marked complete.
- `research/T18/REPORT_426.md`: this report.

## 3. Gaps and error text

No residual statement, missing threaded fact, or final compiler error.
The correction's kinematic facts are available through `.potential`.
Raw packet pressure smoothness is unnecessary because the pressure sum equals
reference pressure plus normalized packet pressure on the solution slab.
Exact resolved compiler messages are recorded in `ATTEMPTS_U2_U4.md`.

The theorems assemble the given records; they do not construct a scaling or
correction record. Their separate T15/T17 non-vacuity work remains outside
this lane, as in U1. No existing Lean module was edited, and no named input,
admission, extra axiom, or heartbeat override was introduced.

## 4. Commands and results

Every Lean command ran from `verification/`, after sourcing
`scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`.

| Command | Result |
|---|---|
| `lake build NSFormalization.Section3.T18.ForceClass NSFormalization.Section3.T18.Kinematics NSFormalization.Section3.T18.Divergence` | pass, 0 errors |
| `lake env lean ../formalization/NSFormalization/Section3/T18/ForceClass.lean` | pass, 0 output |
| `lake env lean ../formalization/NSFormalization/Section3/T18/Kinematics.lean` | pass, 0 output |
| `lake env lean ../formalization/NSFormalization/Section3/T18/Divergence.lean` | pass, 0 output |
| `lake env lean ../research/T18/probes/u2_u4_closes.lean` | pass, 0 output |
| `lake env lean ../research/T18/axioms_u2_u4.lean` | pass; 17 exact standard-three-axiom lines |
| `make check` | pass, including 13 policy tests and 45-item work queue |
| `lake test` | pass, registered contract suite |
| `make test-mutations` | pass; implementation refactor accepted, three bad mutations rejected |
| `git diff --check` | pass |

Build output replays existing dependency warnings; the three new modules
produce no warnings. The repository architecture check retains its existing
source-hash/admission inventory and exits successfully.
