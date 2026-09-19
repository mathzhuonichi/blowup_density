# Lane 471-T24-Ub7-assembly-registration — T24b Ub7: assemble the 30-field `MultipleRegionsAPI`, close `multipleRegionsStatement`, register `T04.multiple_regions`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof/registration worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/471-T24-Ub7-assembly-registration` (git branch `erenup/471-T24-Ub7-assembly-registration`, = `origin/erenup/integration-section3` after lanes 467 (canonical record + Ub1–Ub3), 468 (Ub4) and 469 (Ub5+Ub6) merged).
Read `CLAUDE.md` (contract import rules; bindings bridge by `rfl`/fieldwise conversions; `Tests` = `warningAsError`), **`research/T24/T24_SPLIT.md`** (§0, unit Ub7, §2 ledger), `research/T24/RECONCILIATION.md` (T24b rulings; the bounded-domain/no-slip omission to record
in `scope`), `Section3/T24/Multiple.lean` (canonical `MultipleRegionsAPI` 30 fields, `multipleRegionsStatement`), `MultipleComponents.lean` (`RegionsData`, Ub1–Ub3), `MultipleAssembled.lean` (Ub4: `assembledVelocity/Pressure/Force`, `solution`, `solution_pin`,
`force_mem`, `rest`), `MultipleRegions.lean` (Ub5/Ub6: `region_agreement`, `region_blowup`, `energy_bound`, `dissipation_bound` — if lane 469 defined its own `assembledVelocity`, reconcile by `rfl`), `research/T24/REPORT_{467,468,469}.md`, the registration
pattern of `research/T24/REPORT_430.md` + `verification/{Contracts/V1,Bindings,Tests}/AffineVariation.lean` and `REPORT_420.md` + `ConservativeForcing.lean` (T24 leaf contracts `T04.affine_variation`, `T04.conservative_forcing`), `research/T24/Spec.lean:1140-1340`
(the Spec's `PacketImportAPI`-indexed spelling of the record and statement; the probe `research/T24/probes/multiple_api_on_canonical.lean` from lane 467), `verification/contracts.json`, `collaboration/work_items.json` (T24 item: append the id), and the top 40
lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`. Build the closure first
  (`lake build NSFormalization.Section3.T24.MultipleAssembled NSFormalization.Section3.T24.MultipleRegions`).
- No `sorry`/`admit`/`axiom`/`native_decide`; no placeholder fields; existing `Contracts/V1/*` and `Tests/*` untouched. Contract statements token-for-token the canonical ones (docstrings cite `03-torus.tex:668-740`).
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line.

## Goal
1. `Section3/T24/MultipleAssembly.lean`: `def multipleRegionsAPI (d : RegionsData …) : MultipleRegionsAPI …` (all 30 fields from Ub1–Ub6) and `theorem multipleRegionsStatement_holds : multipleRegionsStatement` in the canonical shape (read it: it quantifies the
   raw packet + clauses, `T`, `N`, regions with `region_interior`/`regions_disjoint` and concludes `Nonempty (MultipleRegionsAPI …)` — build `RegionsData` from the hypotheses).
2. Contract trio `verification/Contracts/V1/MultipleRegions.lean` / `Bindings/MultipleRegions.lean` / `Tests/MultipleRegions.lean` (the Spec's `PacketImportAPI`-indexed record restated token-for-token over registered `PacketImportAPI`/`PlacementData`/`ScalingAPI`
   (`Contracts/V1/Scaling3.lean`), the statement, the binding through the raw projections as lane 467's probe does, the `checked…` test). Registry entry `T04.multiple_regions` (`version: 1`, `parent_task: "T04"`, honest `scope` incl. the no-slip omission),
   `work_items.json` T24 `contracts` += `"T04.multiple_regions"`, `python3 experiments/tasks.py render`.
3. Non-vacuity: `research/T24/probes/multiple_nonvacuity.lean` — `N = 1`, one region (centre `(1/2,1/2,1/2)`, radius `1/4`), the registered nonzero packet (`Bindings.packetImportFamily.select 1 one_pos` or the raw `Bindings.packet` clauses), `T = 1`: obtain the
   `MultipleRegionsAPI` inhabitant and read off `region_blowup 0`.
Deliverables: the modules, the probe, `research/T24/axioms_ub7.lean`, `research/T24/ATTEMPTS_UB7.md`, Ub7 status line in `T24_SPLIT.md`.

## Gates
`lake build NSFormalization.Section3.T24.MultipleAssembly`, `make check`, `make test` (new `checked…` line prints `standard logical axioms only`), `make test-mutations`, `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3`
(registered count +1, `base_compatibility_checked: true`), the probe, the axioms file.

## Report
Commit on your branch; end with four parts (what was registered with exact statements / files / gaps / commands and results). Also write it to `research/T24/REPORT_471.md`.
