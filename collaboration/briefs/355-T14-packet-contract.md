# Lane 355-T14-packet-contract — register the T14 packet import + `eq:packetenergy` contract `T01.packet_import` v1 (40th contract)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) contract-registration worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/355-T14-packet-contract` (git branch `erenup/355-T14-packet-contract`, based on
`origin/erenup/integration-section3` after #318: it contains `formalization/NSFormalization/Section3/T14/PacketEnergy.lean`
(`accumulatedForce`, `energy_le_work_of_packet`, `work_eq_square_of_packet`) and the probe `research/T14/probes/api_on_canonical.lean`, which
restates `research/T14/Spec.lean` verbatim and closes `packetImportStatement` / builds `PacketImportFamily` from `BlowupDensity.Bindings.packet`).
Read `CLAUDE.md` (contract import rules, frozen `Contracts/V1`/`Tests`, `ensure_ascii=False`), the registered Section 3 contracts as templates —
`verification/Contracts/V1/TorusData.lean` + `Bindings/TorusData.lean` + `Tests/TorusData.lean` (lane 275) and the entries `T01.torus_data`,
`T01.torus_local_theory` in `verification/contracts.json` (scope wording) — the Section 4 packet contract `Contracts/V1/Packet.lean` +
`Bindings/Packet.lean` (`packet ν hν`, `l2Sq_eq`, `dissipation_eq`), `research/T14/{Spec.lean,RECONCILIATION.md,COMPARISON.md,REPORT_346.md,
REVIEW_346-T14-packet-energy.md}`, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/placeholder `Prop` fields; do not modify existing `Contracts/V*`, `Tests/*`, `formalization/` modules.
  `Contracts/*` import only `Mathlib`/`Lean`/`Init`/`Contracts.*` (+ the whitelist in `experiments/check_contracts.py`); every restated
  definition gets an `rfl` bridge in `Bindings/`. `Tests/` is `warningAsError`: import only through `Bindings`.
- No goal repackaging: the registered `declaration` must be an actual term of the contract's family/statement built from `Bindings.packet`
  and the T14 theorems, not a hypothesis.

## Deliverables
1. `verification/Contracts/V1/PacketImport.lean` (namespace `BlowupDensity.Contracts.V1`, `import Contracts.V1.Packet` — the contract reuses
   the registered `PacketAPI ν` literally, no periodic proxy): restate **token-for-token from `research/T14/Spec.lean`** (only the namespace
   changes; keep the docstrings and paper citations) `accumulatedForce`, `structure PacketEnergyAPI {ν} (P : PacketAPI ν) : Prop` (fields
   `energy_le_work`, `work_eq_square`), `structure PacketImportAPI (ν) extends PacketAPI ν` (field `energy`), `def packetImportStatement : Prop`,
   `structure PacketImportFamily`. Header docstring: what this contract asserts (`lem:packetenergy`, `paper/sections/02-preliminaries.tex:127-153`,
   the packet of `01-introduction.tex:15-29`; consumed by T15 placement `03-torus.tex:101-123`).
2. `verification/Bindings/PacketImport.lean`: `theorem accumulatedForce_eq : Contracts.V1.accumulatedForce = NSFormalization.Section3.T14.accumulatedForce := rfl`
   (or pointwise if implicit parameters need it — say which), `def packetImportFamily : Contracts.V1.PacketImportFamily` (select `ν hν :=
   { toPacketAPI := Bindings.packet ν hν, energy := ⟨energy_le_work_of_packet …, work_eq_square_of_packet …⟩ }` exactly as the probe does; transport
   through `l2Sq_eq`/`dissipation_eq`), and `theorem packetImport : Contracts.V1.packetImportStatement`.
3. `verification/Tests/PacketImport.lean`: `checkedPacketImport` (bundle the family and the statement), `run_cmd TestSupport.checkAxioms`, a
   conformance `example` restating each field against `research/T14/Spec.lean`, and a non-vacuity `example` (`(packetImportFamily.select ν hν).velocity = (Bindings.packet ν hν).velocity := rfl`).
4. Registry entry `T01.packet_import` (`parent_task: "T01"`, `version: 1`, `specification`/`binding_module`/`test_module`/`declaration`/`enabled`
   exactly in the shape of `T01.torus_local_theory`; honest `scope`: the whole-space packet is the registered `I01.packet` witness (Section 4,
   `Bindings.packet`), T14 adds exactly the two `eq:packetenergy` relations with the factors `2ν` and `2`, `accumulatedForce` as the `Ioo 0 t`
   set integral, both proved from the vendor `CompactEnergy` energy balance + `Paper1/ScalarEnergy.sqrt_energy_le_primitive`; periodization is
   not part of it), `ensure_ascii=False, indent=2`, additions only. Ledger: `python3 experiments/tasks.py claim T14 erenup && python3 experiments/tasks.py render`,
   and add `T01.packet_import` to T14's `contracts` in `collaboration/work_items.json` in the shape T10/T11 use (then render again, `make check`).
5. Records: `research/T14/ATTEMPTS_CONTRACT.md`, conformance `research/T14/axioms_contract.lean`, `research/T14/COMPARISON.md` §"Registered",
   report `research/T14/REPORT_355.md`.

## Gates (paste outputs)
`scripts/gates.sh` from the worktree root with `BASE_REF=origin/erenup/integration-section3` (`make check`, `make test`, `make test-mutations`);
`python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3` (exit 0, `registered_contracts: 40`, `base_compatibility_checked: true`);
the axioms file (every declaration `[propext, Classical.choice, Quot.sound]`); `git diff --stat verification/contracts.json` (additions only).

## Report
Commit on your branch (separate commits for the ledger claim and the contract if the ledger accepts the claim); end with four parts (what is registered, with
field counts / files / gaps / commands and results). Also write it to `research/T14/REPORT_355.md`.
