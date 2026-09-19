# Lane 469-T24-Ub5-Ub6-regions-energy — T24b Ub5 (`region_agreement`, `region_blowup`) and Ub6 (`energy_bound`, `dissipation_bound`) for the assembled velocity

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/469-T24-Ub5-Ub6-regions-energy` (git branch `erenup/469-T24-Ub5-Ub6-regions-energy`, = lane 467's branch (in review) + `origin/erenup/integration-section3`). Lane 468 works **in parallel** on Ub4
(`solution`); you do NOT need it: state everything about the explicit sum `finiteVelocitySum (fun j ↦ (d.component j).velocity)` (define `assembledVelocity d` locally with that body — lane 468 defines the same term; the lead will reconcile by `rfl`).
Read `CLAUDE.md`, **`research/T24/T24_SPLIT.md`** (§0; §1 T24b units Ub5/Ub6 verbatim; ⑧ in `research/T24/RECONCILIATION.md` §4), `research/T24/REPORT_467.md` + `Section3/T24/Multiple.lean` (exact statements of `region_agreement`, `region_blowup`
(`SpeedUnboundedAtOn T (ball (regionCenter j) (regionRadius j)) assembled_velocity`), `energy_bound : (energyEssSupT T u)^2 ≤ ofReal (M^2 * Σ_j ε j)`, `dissipation_bound : (energyGradientT T u)^2 = ofReal (D^2 * Σ_j ε j)`), `Section3/T24/MultipleComponents.lean`
(`RegionsData`, `component_support`, `component_force_support`, `eps_admissible`, `eps_time`, `placement_chart`), `Section3/T15/Blowup.lean` (`unboundedSpeed` — the single-packet blow-up in the chart ball; read the exact statement and how the ball relates to
`x₀`/`chartRadius`), `Section3/T15/Energy.lean` (`packetEnergyIdentity` = `ε^{1/2}·M`-type slice energy, `packetDissipationIdentity`, `energySlices_memLp`), `Section3/T15/Mixed.lean` (`eLpNorm_torusLift_eq_volume`, cube integration), the registered
`energyEssSupT`/`energyGradientT`/`energyENormT` (`Contracts/V1/TorusLocalTheory.lean:230-260` and the canonical copies in `Section3/T10`), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`. Build the closure first
  (`lake build NSFormalization.Section3.T24.MultipleComponents NSFormalization.Section3.T15.Blowup NSFormalization.Section3.T15.Energy`).
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub; a stub is rejected outright.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line. Record every failed approach with its exact error text in the ATTEMPTS file.

## Goal
New module `formalization/NSFormalization/Section3/T24/MultipleRegions.lean` (namespace `NSFormalization.Section3.T24`, `namespace RegionsData`):
- **Ub5**: `theorem region_agreement : ∀ j, ∀ t ∈ Ico 0 d.T, ∀ x ∈ ball (d.regionCenter j) (d.regionRadius j), assembledVelocity d (t, x) = (d.component j).velocity (t, x)` — on `B_j ⊆ fundamentalCube` (from `region_interior`) every other component vanishes
  (`component_support` at `i ≠ j` + `regions_disjoint`), so the sum collapses (`Finset.sum_eq_single`). `theorem region_blowup : ∀ j, SpeedUnboundedAtOn d.T (ball …) (assembledVelocity d)` — transfer `(d.scaling j).unboundedSpeed` (or the T15
  `Blowup.lean` theorem it wraps) through `region_agreement` and `placement_chart` (the packet's blow-up ball sits inside `B_j`; check the exact ball in `unboundedSpeed`).
- **Ub6**: `theorem energy_bound : (energyEssSupT d.T (assembledVelocity d))^2 ≤ ENNReal.ofReal (M^2 * Σ j, d.ε j)` and `theorem dissipation_bound : (energyGradientT d.T (assembledVelocity d))^2 = ENNReal.ofReal (D^2 * Σ j, d.ε j)` (constants exactly as
  in `Multiple.lean`; the split writes `D` for the dissipation constant — use the field's letter). Route: disjoint supports on the cube (`component_support`, `regions_disjoint`) give slice-wise additivity `‖Σ_j U_j(t)‖²_{L²(T³)} = Σ_j ‖U_j(t)‖²` and
  `‖∇Σ_j U_j(t)‖² = Σ_j ‖∇U_j(t)‖²` (cross terms integrate to zero because products of disjointly supported functions vanish pointwise — for the gradient use that `∇U_i` is supported in `tsupport U_i`); then `packetEnergyIdentity` (`= ε_j^{1/2}·M`
  per slice, so squares give `ε_j M²`) and `packetDissipationIdentity` (`= ε_j^{1/2}·D`) — read their exact forms (they may be stated as `ENNReal` equalities of `eLpNorm`s or as real identities) and the exact definitions of `energyEssSupT` (ess-sup in time of
  the slice `L²` norm) and `energyGradientT` (`L²_tL²_x` of the gradient) to match. `essSup` of a sum bounded by the sum of the per-slice bounds; the dissipation is an equality.
Deliverables: the module, `research/T24/probes/regions_energy_closes.lean` (four fields by `exact` against `Multiple.lean` instantiated at `d`), `research/T24/axioms_ub5_ub6.lean`, `research/T24/ATTEMPTS_UB5_UB6.md`, Ub5/Ub6 status lines in `T24_SPLIT.md`.
If one of the four does not close in time, deliver the rest and the exact residual with error text.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T24.MultipleRegions` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (statements / files / gaps with error text / commands and results). Also write it to `research/T24/REPORT_469.md`.
