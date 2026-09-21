# Lane 459-T15-U15-assembly-registration — T15 U15: `PlacementData` witness, `ScalingAPI` assembly (21 fields), `scalingStatement`, register `T02.scaling`

(Worktree to be created from the merged base once lanes 454 (U11) and 458 (U14) land.) You are a Lean 4 (v4.34.0-rc2 + Mathlib) worker in
`/data_8T/ping/blowup_density/.claude/worktrees/459-T15-U15-assembly-registration` (branch `erenup/459-T15-U15-assembly-registration`). On the base: every T15 unit module
`Section3/T15/{Bridges,ParsevalZero,HaarBridge,Scaling (U-CAN: raw-field PlacementData + ScalingAPI :106-460, scalingStatement :470-…), Placement (U2), SingleCopy (U3), Energy (U4), Mixed (U5), Blowup (U6),
ForceMem (U7), Equation (U8), SobolevPath (U9), Pressure (U10), Solution (U11), SobolevBound (U12/U13), Convergence (U14)}.lean`, the registered `I01.packet`/`PacketImport` contracts
(`Contracts/V1/Packet.lean`, `PacketImport.lean`, `Bindings/Packet.lean`: `Bindings.packet ν hν`, `PacketAPI.force_support` gives `HasCompactSupport`), the registered `T02.localization` (`Contracts/V1/Localization.lean`,
`Bindings/Localization.lean` — the T13 `LocalizationAPI` inhabitant the `localization` field needs), `Section3/T13/Assembly.lean`. Read `CLAUDE.md` (contract import rules; `rfl` bridges; structure exceptions →
fieldwise conversions; `ensure_ascii=False, indent=2`), **`research/T15/T15_SPLIT.md` §0 and unit U15** (`:240-…`), `research/T15/Spec.lean:560-643` (`PlacementData`), `:650-920` (`ScalingAPI`, 21 fields,
`scalingStatement :919`: `Nonempty (ScalingAPI (𝔉.select ν hν) place)` — read the exact quantifiers), `research/T15/RECONCILIATION.md`, every `research/T15/REPORT_{376,384,421,439,442,446,447,450,454,456,458}.md`
§1 (the exact raw clauses each unit theorem takes: velocity/pressure/force support, smoothness on the slab, `SpeedUnboundedAtOne`, `CompactPositiveTimeSupport`, the `I03.PacketData` bundle, …), the
registration precedents (`Contracts/V1/TorusLocalTheory.lean` trio; lane 430's `AffineVariation` trio; lane 453's `Correction3` trio), `verification/contracts.json`, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`/placeholder fields; no edits to existing modules (new files plus registry/work-items additions); every restated definition bridged by `rfl` or fieldwise
  conversion; every declaration prints exactly `[propext, Classical.choice, Quot.sound]`.

## Deliverables
1. `formalization/NSFormalization/Section3/T15/Assembly.lean`: `def scalingAPI … : ScalingAPI …` assembling the 21 fields from the unit theorems for any raw packet data satisfying the raw clauses
   (list the union of clauses; the `localization` field from the canonical T13 witness); a **canonical `PlacementData` constructor** `placementData` (data, not `∃`) for any raw packet **and any prescribed horizon `T` with `0 < T` (explicit parameter; `(placementData … T hT).T = T` by `rfl` — T19 must place at the horizon of a given reference)** (compact carrier `K`, force
   support projection compact): choose `Kstar ⊇ K ∪ pr_x (tsupport f)` compact, a chart ball with `closure ⊆ interior fundamentalCube` (centre the cube centre `(1/2,1/2,1/2)`, radius `< 1/2`), `x₀` in it,
   `ε₀` small enough for `eps_time`/`eps_space`; `theorem scalingStatement_holds` in the canonical shape; non-vacuity on the registered nonzero packet (`Bindings.packet` clauses restated in the probe).
2. `verification/Contracts/V1/Scaling3.lean` (name avoids the Section 4 `Scaling.lean`): `PlacementData`, `ScalingAPI`, `scalingStatement` token-for-token from `research/T15/Spec.lean` over the registered
   vocabulary; 3. `verification/Bindings/Scaling3.lean`: bridges/conversions + instance from the canonical assembly at `Bindings.packet ν hν`, `scalingStatement_holds`; 4. `verification/Tests/Scaling3.lean`:
   `checkedScaling3`, `run_cmd TestSupport.checkAxioms`, conformance `example`s for three fields, non-vacuity; 5. registry entry `T02.scaling` (`version: 1`, `parent_task` per the T15 work item, honest
   `scope`), `work_items.json` + `python3 experiments/tasks.py render`; records `research/T15/ATTEMPTS_U15.md`, `research/T15/axioms_u15.lean`, U15 status in `T15_SPLIT.md`.

## Gates (paste outputs)
`scripts/gates.sh` from the worktree root; `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3` (exit 0, `registered_contracts` = base + 1, `base_compatibility_checked: true`);
the axioms file; `git diff --stat verification/contracts.json`.

## Report
Commit on your branch; end with four parts. Also write it to `research/T15/REPORT_459.md`.

## Lead note (2026-09-19 13:50Z)
U14 landed in two halves: `Section3/T15/Convergence.lean` (lane 458, `forceConvergence_one`, `q = 1`) and `Section3/T15/ConvergenceTwo.lean` (lane 462, `forceConvergence_two`, `q = 2`, plus the combined `forceConvergence` with the field type). Use the combined theorem for the `forceConvergence` field; read `research/T15/REPORT_{458,462}.md`. Note `alphaT 2 2 = −1/2` (the mixed `q = 2` order-0 quantity diverges; only negative orders converge).
