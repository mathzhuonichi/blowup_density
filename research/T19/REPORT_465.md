# Lane 465 — T19 U13/U14 closure

## 1. Theorems with exact statements

Both theorems are in `NSFormalization.Section3.T19`. Their statements are
literal copies of the canonical `StrongClosureAPI` fields, checked by `exact`
in the probe. In particular, the admissible family clause uses `Ioo` and
quantifies one family before every subcritical Sobolev order.

```lean
theorem simultaneousPairConvergence :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ g : SpaceTimeField, g ∈ forceClassT →
          ∀ δ : ℝ, 0 < δ →
            ∀ reference : ClassicalSolutionT ν a g (T + δ),
              ∃ ε₀ : ℝ, 0 < ε₀ ∧
                ∃ u f : ℝ → SpaceTimeField,
                  (∀ ε ∈ Ioo (0 : ℝ) ε₀,
                    f ε ∈ forceClassT ∧
                    maximalLifespanT ν a (f ε) = ENNReal.ofReal T ∧
                    (∃ w : ClassicalSolutionT ν a (f ε) T, w.velocity = u ε) ∧
                    SingularTrajectoryT ν a T (u ε)) ∧
                  Tendsto
                    (fun ε : ℝ =>
                      energyENormT T (fun z => u ε z - reference.velocity z))
                    (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) ∧
                  (∀ s : ℝ, s < 1 / 2 →
                    Tendsto
                      (fun ε : ℝ => forceSobolevENormT 1 s (fun z => f ε z - g z))
                      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)))
```

```lean
theorem closureInEnergy :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ u : SpaceTimeField, RegularTrajectoryT ν a T u →
          ∀ r : ℝ≥0∞, 0 < r →
            ∃ u' : SpaceTimeField, SingularTrajectoryT ν a T u' ∧
              energyENormT T (fun z => u z - u' z) < r
```

U13 takes `insertion hν ha hg hT hδ reference`: U0 already zero-extends the
reference internally. `extendByZero_velocity_eqOn` gives the identification
on `Ico 0 T` directly, so the older R41 uniqueness detour is unnecessary.
The difference has finite energy by `energyRate`; U5 and the T18 triangle
inequality give finite energy of the inserted velocity. Smoothness supplies
both required slice measurability guards. The two positive powers converge
to zero, and U0 supplies the full `∀ s < 1/2` force limit. U14 extracts a
scale from `Ioo_mem_nhdsGT` and the energy limit and reverses the difference.

Three supporting theorems also close:

```lean
energyENormT_congr_Ico {T : ℝ} {u v : SpaceTimeField}
  (h : EqOn u v (Ico (0 : ℝ) T ×ˢ univ)) :
  energyENormT T u = energyENormT T v

energySlices_of_smooth {T : ℝ} {u : SpaceTimeField}
  (hu : ContDiffOn ℝ ∞ u (Ico (0 : ℝ) T ×ˢ univ)) :
  NSFormalization.Section3.T15.EnergySlicesMemLpT T u

energyENormT_sub_comm (T : ℝ) (u v : SpaceTimeField) :
  energyENormT T (fun z => u z - v z) =
    energyENormT T (fun z => v z - u z)
```

## 2. Files

- `formalization/NSFormalization/Section3/T19/Closure.lean`: five theorems.
- `research/T19/probes/closure_closes.lean`: both literal field types by `exact`.
- `research/T19/axioms_u13_u14.lean`: all five declarations audited.
- `research/T19/ATTEMPTS_U13_U14.md`: failed iterations with exact diagnostics.
- `research/T19/T19_SPLIT.md`: U13/U14 completion status.
- `research/T19/REPORT_465.md`: this report.

No existing Lean module was edited. The pre-existing modification to
`collaboration/briefs/465-T19-U13-U14-closure.md` is excluded from this commit.

## 3. Gaps and error text

No gaps, named inputs, placeholders, forbidden proof shortcuts, or heartbeat
settings. Every declaration prints exactly
`[propext, Classical.choice, Quot.sound]`.

Resolved diagnostics are preserved verbatim in the attempts file: incorrect
namespace for `spatialDerivative`, an overly broad `congr 1` timing out,
local universe inference preventing simplification, beta reduction in an
`EqOn` rewrite, and a final unnecessary tactic-sequencing lint warning.
Final module and probe checks produce zero output.

## 4. Commands and results

All Lean invocations source `scripts/lean-env.sh`, run from `verification/`,
and use `LEAN_NUM_THREADS=6`.

- `lake build NSFormalization.Section3.T19.DensityEngine`: exit 0, 10658 jobs.
- `lake build NSFormalization.Section3.T19.Closure`: exit 0, 10659 jobs.
  Dependency warnings replayed; the new module has no warnings.
- `lake env lean ../formalization/NSFormalization/Section3/T19/Closure.lean`:
  exit 0, zero output.
- `lake env lean ../research/T19/probes/closure_closes.lean`: exit 0, zero output.
- `lake env lean ../research/T19/axioms_u13_u14.lean`: exit 0; all five print
  exactly the standard three axioms.
- `make check`: exit 0; contract policy, 13 policy tests and 45 work items pass.
- `lake test`: exit 0, 10978 jobs.
- `make test-mutations`: exit 0; implementation refactor accepted; admission,
  extra axiom and weakened hypothesis rejected.
- `git diff --check`: exit 0. Forbidden-token scan of implementation and
  probe: no matches.

Committed on the assigned branch; no push, merge or rebase.
