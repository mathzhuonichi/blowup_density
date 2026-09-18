# REPORT_425 — T17 U7 force_smooth / force_periodic / force_support (Opus; transcribed by lead from the agent message, report-file guard)

All three U7 fields are closed. Final report.

---

## 1. What was proved

All three canonical `CorrectionAPI` fields of unit U7, at the concrete `correctionData` of unit U2, for `ε ∈ Ioc 0 D.ε₀`. Common binder block (identical on all three, same shape as lane 385's `force_derivative_bound`):

```
(ν : ℝ) {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T δ r : ℝ)
(hvper : IsPeriodicOn univ v) {θ : Space → ℝ} {η : ℝ → ℝ} (O : Set Space) (θR ε₀ : ℝ)
(hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
(hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
(hθsupp : tsupport θ ⊆ ball (0 : Space) θR) (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
(hr2 : r < 1 / 2)
(hεtime : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min T δ)
(hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r)
```

**`force_smooth`** (`ForceSupport.lean:135`):
```
∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀,
  ContDiff ℝ ∞ (correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε)
```

**`force_periodic`** (`:164`):
```
∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀,
  IsPeriodicOn univ (correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε)
```

**`force_support`** (`:191`):
```
∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀,
  tsupport (correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε) ⊆
    Ioo (T - 2 * ε ^ 2) (T + 2 * ε ^ 2) ×ˢ
      periodicSet (ball x₀ (ε * (correctionData v x₀ T θ η O θR ε₀).θRadius))
```
`Metric.ball` — the manuscript's **open** ball; no closed-ball weakening (the elaborator's printed type in the mutation errors below confirms it).

**Where `hv` enters** (the only extra premise, the documented G1 of `research/T17/SPEC_ISSUES.md`) — exactly two uses:
1. `force_smooth` only: Paper1's `physicalForce_smooth` needs *global* `ContDiff ℝ ∞ v` for the single-copy force.
2. all three: `Transport.force_eq` / `correctionForce_periodic` require `ContDiffOn ℝ ∞ v (Ioo 0 (T+δ) ×ˢ ball x₀ r)`, discharged by `hv.contDiffOn`.
`force_support`'s own ingredients (`physicalForce_compact`, `correctionForce_support`, `physical_support`) need no regularity of `v`; `hv` is there only for `force_eq`.

Two supporting theorems, both new, no named input, no placeholder:
- `latticeLift_spaceSupport` (`:77`) — space-time companion of T16's `latticeLift_sliceSupport_closed`: for `C` closed with `C ⊆ ball x₀ ρ` and `w`'s slice support in `C`, `tsupport (latticeLift w) ⊆ univ ×ˢ periodicSet C`.
- `source_force_tsupport` (`:119`) — `tsupport (Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε)) ⊆ Ioo (T-2ε²) (T+2ε²) ×ˢ ball x₀ (ε*θR)`.

## 2. What exists in Lean now

- `/data_8T/ping/blowup_density/.claude/worktrees/425-T17-U7-force-support/formalization/NSFormalization/Section3/T17/ForceSupport.lean` — 246 lines, new module, namespace `NSFormalization.Section3.T17`. No existing module edited.
- `/data_8T/ping/blowup_density/.claude/worktrees/425-T17-U7-force-support/research/T17/probes/force_support_closes.lean` — 205 lines. Three `field_*` theorems restating the Spec fields at the concrete data, closed by `exact`; three `example`s that *project* `A.force_smooth` / `A.force_periodic` / `A.force_support` out of a hypothetical `CorrectionAPI ν place v r δ (correctionData v place.x₀ place.T …)` into exactly the delivered statements (two-sided type conformance against the canonical record); `fields_at_placement` supplying all three at `place.x₀`/`place.T`; `nonvacuous_force_support` instantiating all three on T16's `exists_originCutoff`/`exists_timeCutoff`/`exists_threshold` at a nonzero, divergence-free, periodic constant reference.
- `/data_8T/ping/blowup_density/.claude/worktrees/425-T17-U7-force-support/research/T17/axioms_u7.lean`
- `/data_8T/ping/blowup_density/.claude/worktrees/425-T17-U7-force-support/research/T17/ATTEMPTS_U7.md`
- U7 status paragraph appended in `/data_8T/ping/blowup_density/.claude/worktrees/425-T17-U7-force-support/research/T17/T17_SPLIT.md:192-197`
- Commit `4b371373` on `erenup/425-T17-U7-force-support`; working tree clean; nothing pushed/merged/rebased.

I did **not** create `research/T17/REPORT_425.md`: my harness instructions forbid writing report/summary `.md` files, so per the brief's fallback the full report is here.

## 3. Gaps

**No residual statement — all three fields are closed.** Three things the lead should know:

1. **G1 is still open at the spec level, not at this lane's level.** The three theorems carry `hv : ContDiff ℝ ∞ v` explicitly, exactly as U3–U6 do. The canonical `CorrectionAPI` has only `reference_periodic`, so assembly unit U12 must still either add `reference_smooth` or truncate the reference (`SPEC_ISSUES.md` option (a)/(b)). Strictly, only `force_smooth` needs the *global* form; `force_periodic`/`force_support` would survive a chart-truncation route with local smoothness alone.
2. **The brief's route for `force_support` does not work as written.** `T16.latticeLift_sliceSupport:275` (brief said `:271`) cannot supply the field: (a) it requires a strictly larger radius `ρ < r`, so at `ρ = ε·θR` it returns `periodicSet (ball x₀ r)` with `r > ε·θR`, which is *not* the field's set; (b) it bounds one spatial slice's `tsupport`, while the field bounds the space-time `tsupport`, and slicewise bounds do not compose into the space-time one. `latticeLift_spaceSupport` (§0 of the new module) is the fix; it is a candidate for promotion into `Section3/T16/` by a later maintenance lane, since it is a general lattice-lift fact, not a T17 fact. I did not move it because the brief forbids editing existing modules.
3. **Brief line numbers are off by 4 in `Section3/T16/LatticeLift.lean`** (verified with `sed -n`): `latticeLift_smooth` is at `:120` not `:116`, `latticeLift_periodic` `:128` not `:124`, `latticeLift_timeSupport` `:251` not `:247`, `latticeLift_sliceSupport` `:275` not `:271`. Paper1 `physicalForce_smooth:22` / `physicalForce_compact:37` are correct, but the namespace is `NSFormalization.Paper1.CorrectionForceNorms` while the file is `Paper1/CorrectionVectorNorms.lean`.

Failed approaches (all recorded in `ATTEMPTS_U7.md`):
- `latticeLift_sliceSupport` directly — rejected for the two reasons above; using it would have delivered a weakened radius, which the brief forbids.
- `closure (A ×ˢ B) = closure A ×ˢ closure B` with `B = periodicSet C` — reduces to `IsClosed (periodicSet C)` for compact `C`, a locally-finite-union fact with **no lemma in the tree** (`grep -rn "periodicSet" formalization/` yields only `periodicSet`, `periodicSet_mono`, and the two slice lemmas); proving it from scratch would re-derive what `periodize_locally_eq_sum` already provides.
- Case split with `notMem_tsupport_iff_eventuallyEq` on `z.1 ∉ Ioo …` / `z.2 ∉ periodicSet …` — the time half is fine, the spatial half needs a *space-time* neighbourhood on which the lift vanishes and the slice lemma only yields a spatial one.
- What unblocked it: `periodize_locally_eq_sum` (`vendor/NavierStokesAndEuler/NavierStokes/PeriodicLocalization.lean:136`) is already stated at a space-time point, so T16's `latticeLift_sliceSupport_closed` proof (`Section3/T16/Assembly.lean:201`) transposes verbatim.

## 4. Commands and results

All from `.../425-T17-U7-force-support/verification` after `. ../scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`.

| Command | Result |
|---|---|
| `lake build NSFormalization.Section3.T17.ForceSupport` | `✔ [9362/9362] Built NSFormalization.Section3.T17.ForceSupport (2.7s)` / `Build completed successfully (9362 jobs).` — 0 errors (warnings are pre-existing, from replayed upstream modules only) |
| `lake env lean ../formalization/NSFormalization/Section3/T17/ForceSupport.lean` | no output, exit 0 |
| `lake env lean ../research/T17/probes/force_support_closes.lean` | 5 lines, each `depends on axioms: [propext, Classical.choice, Quot.sound]` (`field_force_smooth`, `field_force_periodic`, `field_force_support`, `fields_at_placement`, `nonvacuous_force_support`); no errors, so the three `A.force_*` conformance `example`s typechecked |
| `lake env lean ../research/T17/axioms_u7.lean` | 5 lines, each `[propext, Classical.choice, Quot.sound]` (`latticeLift_spaceSupport`, `source_force_tsupport`, `force_smooth`, `force_periodic`, `force_support`) |
| `make check` (repo root) | passes: architecture checks JSON, `test_contract_policy.py` `Ran 13 tests … OK`, `check_work_queue.py` `45 work items: ownership, contract registration and task cards consistent.` |
| `make test` (repo root) | exit 0, `[10859/10859]`, every registered contract `checked; standard logical axioms only` |
| `grep -nE "sorry\|admit\|native_decide\|^axiom \|maxHeartbeats"` on the three new Lean files | no matches (exit 1) |

Negative probes (run from `/tmp/u7mut`, deliberately not committed), both **failed as required**:
- narrowed time window `Ioo (T - ε^2) (T + ε^2)`: `error: Type mismatch … has type … Ioo (T - 2 * ε ^ 2) (T + 2 * ε ^ 2) ×ˢ periodicSet (ball x₀ (ε * (correctionData v x₀ T θ η O θR ε₀).θRadius)) but is expected to have type … Ioo (T - ε ^ 2) (T + ε ^ 2) ×ˢ …`
- `periodicSet` dropped: `error: Type mismatch … ×ˢ periodicSet (ball x₀ (ε * … .θRadius)) but is expected to have type … ×ˢ ball x₀ (ε * … .θRadius)`

Both error texts print the delivered statement with `ball` (open), never `closedBall`.
