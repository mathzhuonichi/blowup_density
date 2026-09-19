# Lane 455-T18-U12-assembly-registration — T18 U12: assemble `PeriodicInsertionAPI` (45 fields) from U1–U11, close `periodicInsertionStatement`, register `T03.periodic_insertion`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) worker in
`/data_8T/ping/blowup_density/.claude/worktrees/455-T18-U12-assembly-registration` (branch `erenup/455-T18-U12-assembly-registration`). On the base: the whole canonical T18 layer
`Section3/T18/{Insertion (U1: InsertionData, velocity/pressure/force, formulas, ε₀, eps_*, delta_pos, reference_force_mem, initial_mem), ForceClass (U2), Kinematics (U3), Divergence (U4), CrossTransport
(U5), Momentum (U6), Support (U7: velocityDifference_support takes the explicit raw premise `hsupp`), Lifespan (U8), EnergyRate (U9: energyRate takes explicit `hM`/`hD`), MixedRate (U10), SobolevRate
(U11)}.lean`, the probes `research/T18/probes/{insertion_closes,u2_u4_closes,u5_u6_closes,u7_closes,u8_closes,u9_u10_closes,u11_closes}.lean` (each discharges the Spec-form fields from the canonical
theorems through the U1 conversions — **reuse their conversion code**), the registered contracts `Contracts/V1/{TorusData,TorusLocalTheory,Packet,PacketImport,LocalPotential,Localization,MeanZeroCalculus,
BoundedDomainNorm,AffineVariation,ConservativeForcing}.lean` and, if landed, `Contracts/V1/Correction3.lean` (lane 453, `T02.correction`) / `CriticalRegularity.lean` (lane 451) — check `verification/contracts.json`.
Read `CLAUDE.md` (contract import rules; `rfl` bridges; structure exception → fieldwise conversions; `ensure_ascii=False, indent=2`), **`research/T18/T18_SPLIT.md` §0 and unit U12** (`:203-209`),
`research/T18/Spec.lean:1658-1985` (the `PeriodicInsertionAPI` text the contract must match token-for-token, its 11 parameters incl. `scaling : ScalingAPI P place` and `correction : CorrectionAPI ν place
reference.velocity r δ D` in the Spec's own namespaces, and `periodicInsertionStatement :1977`), `research/T18/RECONCILIATION.md` §2 (threading), every `research/T18/REPORT_{422,426,433,435,436,443,445}.md`
§1 (exact theorem signatures, incl. the explicit raw premises of U7/U9 and how the probes discharge them from `PacketImportAPI.velocity_support`, `energy_isLUB`, `dissipation_eq`), the registration
precedents (`Contracts/V1/TorusLocalTheory.lean` trio; lane 430's `AffineVariation` trio for a record parameterised by a registered packet), `verification/contracts.json`, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`/placeholder fields; no edits to existing modules (new files plus registry/work-items additions); every restated definition bridged by `rfl` or fieldwise
  conversion; every declaration prints exactly `[propext, Classical.choice, Quot.sound]`.

## Deliverables
1. `formalization/NSFormalization/Section3/T18/Assembly.lean`: the canonical 45-field record type (or reuse the Spec-shaped canonical structure if U1 defined one — read `Insertion.lean`) assembled from
   U1–U11 for any `data : InsertionData` plus the explicit raw premises (`hsupp`, `hM`, `hD`) — bundle those three into the assembly theorem's hypotheses; `theorem periodicInsertionStatement_holds`
   in the canonical shape (`∀ ν, 0 < ν → ∀ raw packet fields … place scaling a g r δ D reference correction, hypotheses …, Nonempty (…)`). **Because `scaling`/`correction` are threaded parameters the
   statement closes now**; the concrete end-to-end non-vacuity example (an inhabited `scaling`/`correction`/`reference`) is gated on T15 U15 and T17 U12 — state exactly what is missing and stage
   it as a documented `example` with the `sorry`-free hypotheses spelled out (no `sorry`: instead a theorem `nonvacuity_of_witnesses : (∃ scaling correction reference …) → Nonempty …`).
2. `verification/Contracts/V1/PeriodicInsertion.lean`: `PeriodicInsertionAPI` token-for-token from `research/T18/Spec.lean` over the registered vocabulary (`PacketImportAPI`, the registered T15/T17
   contracts if landed — otherwise restate `PlacementData`/`ScalingAPI`/`CorrectionAPI` verbatim with provenance and note that they are superseded by the registrations of T15 U15 / lane 453),
   `periodicInsertionStatement`.
3. `verification/Bindings/PeriodicInsertion.lean`: bridges/conversions; the instance from the canonical assembly; `periodicInsertionStatement_holds`.
4. `verification/Tests/PeriodicInsertion.lean`: `checkedPeriodicInsertion`, `run_cmd TestSupport.checkAxioms`, conformance `example`s for three fields, the staged non-vacuity.
5. Registry entry `T03.periodic_insertion` (`version: 1`, `parent_task` per the T18 work item, honest `scope`: threaded records, explicit raw premises, non-vacuity gate), `work_items.json` +
   `python3 experiments/tasks.py render`; records `research/T18/ATTEMPTS_U12.md`, `research/T18/axioms_u12.lean`, U12 status in `T18_SPLIT.md`.

## Gates (paste outputs)
`scripts/gates.sh` from the worktree root; `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3` (exit 0, `registered_contracts` = base + 1, `base_compatibility_checked: true`);
the axioms file; `git diff --stat verification/contracts.json`.

## Report
Commit on your branch; end with four parts. Also write it to `research/T18/REPORT_455.md`.
