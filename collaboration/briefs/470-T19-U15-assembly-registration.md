# Lane 470-T19-U15-assembly-registration — T19 U15: assemble the four density records, close the four statements, register `T03.density`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof/registration worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/470-T19-U15-assembly-registration` (git branch `erenup/470-T19-U15-assembly-registration`, = lane 465's branch (464/466 merged into integration; 465 in the merge queue) + `origin/erenup/integration-section3`).
Read `CLAUDE.md` (contract import rules: `Contracts/*` import only `Mathlib`/`Lean`/`Init`/`Contracts.*` + the canonical-module whitelist; bindings bridge canonical ↔ contract by `rfl` or fieldwise conversions; `Tests` = `warningAsError`),
**`research/T19/T19_SPLIT.md`** (§0 and the U-CAN/U0/U7–U14 status lines), `research/T19/RECONCILIATION.md` (§3 decisions, §4 ledger — the registered vocabulary the records are stated over), `Section3/T19/Density.lean` (canonical `PeriodicDensityAPI`,
`MixedRegionAPI`, `StrongClosureAPI`, `ProjectionAPI` — all `Prop`, 13 fields — and `periodicDensityStatement`, `mixedRegionStatement`, `strongClosureStatement`, `projectionStatement`), the proved fields: `Section3/T19/Bookkeeping.lean` (U1–U6),
`DensityEngine.lean` (U7–U9), `Closure.lean` (U13–U14), `Projection.lean` (U10–U12), the registration pattern of the last three registrations (`research/T15/REPORT_459.md` + `verification/{Contracts/V1,Bindings,Tests}/Scaling3.lean`;
`research/T18/REPORT_455.md` + `PeriodicInsertion.lean`; `research/T20/REPORT_451.md` + `CriticalRegularityT.lean`; note the `T` suffix convention when a whole-space module name is already taken — `Contracts/V1/Density.lean`? check `ls verification/Contracts/V1`
and pick `DensityT.lean` if the unsuffixed name exists), `verification/contracts.json` (entry shape: `id`, `version`, `parent_task`, `statement`, `binding`, `test`, `scope`, …), `experiments/check_contracts.py`, `collaboration/work_items.json` (T19 item:
add the contract id, keep `state`/`owner` consistent with `python3 experiments/tasks.py render`), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`. Build the closure first
  (`lake build NSFormalization.Section3.T19.Projection NSFormalization.Section3.T19.Closure NSFormalization.Section3.T19.DensityEngine`).
- No `sorry`/`admit`/`axiom`/`native_decide`; no placeholder `Prop` fields; existing `Contracts/V1/*` and `Tests/*` untouched. Contract statements are token-for-token the canonical ones (docstrings cite paper lines).
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line.

## Goal
1. `formalization/NSFormalization/Section3/T19/Assembly.lean`: `def periodicDensityAPI : PeriodicDensityAPI`, `mixedRegionAPI`, `strongClosureAPI`, `projectionAPI` (each field := the proved theorem), and `theorem periodicDensityStatement_holds`, `mixedRegionStatement_holds`,
   `strongClosureStatement_holds`, `projectionStatement_holds`.
2. Contract trio `verification/Contracts/V1/<Density module>.lean` (the four `Prop` structures + four statement defs restated token-for-token over the registered vocabulary), `verification/Bindings/<same>.lean` (bridges: `rfl` where the canonical definitions
   are registered ones, fieldwise conversions for `ClassicalSolutionT`, `maximalLifespanT_eq` for the lifespan; the four `…_holds` theorems in the contract's spelling), `verification/Tests/<same>.lean` (`checked…` theorems + `#print axioms` gate as in the
   other tests). One registry entry `T03.density` (`version: 1`, `parent_task: "T03"`, honest `scope`: the four statements, `Prop`, `q = 1` Sobolev density, mixed region, strong closure in `E_T`, projection; note the T18/T17 slab route (G5) in the scope
   text), `work_items.json` T19 `contracts: ["T03.density"]`, `python3 experiments/tasks.py render`.
3. Non-vacuity: the statements are `∀`-shaped `Prop`s over registered classes; add the probe `research/T19/probes/assembly_closes.lean` instantiating `periodicDensityStatement_holds` at the registered zero datum/force (`0 ∈ initialClassT`, `0 ∈ forceClassT` or
   the packet force) with explicit `ν = 1`, `T = 1`, `s = 0` and reading off a concrete `f` — no `True`.
Deliverables: the modules, the probe, `research/T19/axioms_u15.lean`, `research/T19/ATTEMPTS_U15.md`, U15 status line in `T19_SPLIT.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T19.Assembly`, `make check`, `make test` (the new `checked…` lines must print `standard logical axioms only`), `make test-mutations`, `python3 experiments/check_contracts.py --base-ref
origin/erenup/integration-section3` (registered count +1, `base_compatibility_checked: true`), the probe, the axioms file.

## Report
Commit on your branch; end with four parts (what was registered with exact statements / files / gaps / commands and results). Also write it to `research/T19/REPORT_470.md`.
