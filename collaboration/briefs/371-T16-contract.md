# Lane 371-T16-contract — register the T16 local divergence-free cutoff contract `T02.local_potential` v1 (41st contract)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) contract-registration worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/371-T16-contract` (git branch `erenup/371-T16-contract`, based on `origin/erenup/integration-section3` after #330:
`Section3/T16/{LocalPotential,BallPotential,LatticeLift,Assembly}.lean` with `localPotential : localPotentialStatement` proved (all 26 fields of `LocalPotentialAPI`)).
Read `CLAUDE.md` (contract import rules, frozen `Contracts/V1`/`Tests`, `ensure_ascii=False`, **"结构体例外"**: a `structure` restated in a contract is a different inductive type, so the
binding supplies fieldwise conversions + round trips instead of an impossible `rfl` bridge), the registered Section 3 contracts as templates — `verification/Contracts/V1/TorusLocalTheory.lean`
+ `Bindings/TorusLocalTheory.lean` (the `ClassicalSolutionT` conversions `toContract`/`ofContract`) + `Tests/TorusLocalTheory.lean` (lane 340), `Contracts/V1/PacketImport.lean` + bindings/tests
(lane 355), and the registry entries `T01.torus_data` / `T01.torus_local_theory` / `T01.packet_import` in `verification/contracts.json` (scope wording); then `research/T16/Spec.lean`
(the reconciled statement, token-for-token source), `research/T16/probes/api_on_canonical.lean` (the fieldwise conversions Spec ↔ canonical module already written by lane 347 —
reuse their shape), `research/T16/{RECONCILIATION.md,COMPARISON.md,REPORT_347.md,REPORT_351.md,REPORT_352.md,REPORT_358.md,REVIEW_358-T16-assembly.md}`, and the top 40 lines of
`logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/placeholder `Prop` fields; do not modify existing `Contracts/V*`, `Tests/*`, `formalization/` modules.
  `Contracts/*` import only `Mathlib`/`Lean`/`Init`/`Contracts.*` (+ the whitelist in `experiments/check_contracts.py`); every restated `def` gets an `rfl` bridge in `Bindings/`;
  restated `structure`s get fieldwise conversions with both round trips by `rfl`. `Tests/` is `warningAsError`: import only through `Bindings`.
- No goal repackaging: the registered `declaration` must be an actual proof of the contract's statement transported from `NSFormalization.Section3.T16.localPotential`, not a hypothesis.

## Deliverables
1. `verification/Contracts/V1/LocalPotential.lean` (namespace `BlowupDensity.Contracts.V1`, `import Contracts.V1.TorusData` (+ `Contracts.V1.Packet` if the Spec's vocabulary needs it)):
   restate **token-for-token from `research/T16/Spec.lean`** (only the namespace changes; keep docstrings and paper citations) the T16 vocabulary it introduces (`IsPeriodicOn` if not already
   registered — check `TorusLocalTheory.lean`; `latticeVector`, `periodicSet`, `periodicScaledPacket`, `correctedBackground`), `structure CutoffData`, `structure LocalPotentialAPI … : Prop`
   (26 fields), and `def localPotentialStatement : Prop`. Header docstring: what this contract asserts (`lem:potential`, `paper/sections/03-torus.tex:176-217`; consumed by T17/T18).
2. `verification/Bindings/LocalPotential.lean`: `rfl` bridges for every restated `def` (`latticeVector_eq`, `periodicSet_eq`, …; pointwise if implicit parameters need it — say which);
   for `CutoffData` the fieldwise conversions `toContract`/`ofContract` + round-trip lemmas by `rfl`; for `LocalPotentialAPI` the transport `api_toContract : LocalPotentialAPI (module) v U K x₀ r T δ D → Contracts…LocalPotentialAPI v U K x₀ r T δ (toContract D)`
   (fieldwise, all 26 fields defeq — mirror `research/T16/probes/api_on_canonical.lean`'s `api_toModule`/`api_ofModule`), and `theorem localPotential : Contracts.V1.localPotentialStatement`
   from `NSFormalization.Section3.T16.localPotential`.
3. `verification/Tests/LocalPotential.lean`: `checkedLocalPotential` (bundle the transported statement), `run_cmd TestSupport.checkAxioms`, a conformance `example` restating the statement
   against `research/T16/Spec.lean`, and a non-vacuity `example` (a nonzero constant divergence-free `v` on some chart ball, as in `research/T16/probes/assembly_closes.lean`).
4. Registry entry `T02.local_potential` (`parent_task: "T02"` — the T02 bucket "Periodic localization and insertion" of `formalization/blueprint/tasks.json`; `version: 1`;
   `specification`/`binding_module`/`test_module`/`declaration`/`enabled` in the shape of `T01.packet_import`; honest `scope`: the Urysohn cutoffs, threshold, radial potential
   `timePotential` on the chart ball (only local smoothness of `v`), the unit-periodic lattice lift of `physicalCorrection` with all seven `correction_*` clauses incl. `eq:bgzero`;
   the structure exception for `CutoffData`/`LocalPotentialAPI`; no bound on the correction is asserted (that is T17)), `ensure_ascii=False, indent=2`, additions only.
   Ledger: `python3 experiments/tasks.py claim T16 erenup && python3 experiments/tasks.py render`, add `T02.local_potential` to T16's `contracts` in `collaboration/work_items.json`
   (shape as T10/T11/T14), render again, `make check`.
5. Records: `research/T16/ATTEMPTS_CONTRACT.md`, conformance `research/T16/axioms_contract.lean`, `research/T16/COMPARISON.md` §"Registered", report `research/T16/REPORT_371.md`.

## Gates (paste outputs)
`scripts/gates.sh` from the worktree root with `BASE_REF=origin/erenup/integration-section3` (`make check`, `make test`, `make test-mutations`);
`python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3` (exit 0, `registered_contracts: 41`, `base_compatibility_checked: true`);
the axioms file (every declaration `[propext, Classical.choice, Quot.sound]`); `git diff --stat verification/contracts.json` (additions only).

## Report
Commit on your branch (separate commits for the ledger claim and the contract); end with four parts (what is registered, with field counts / files / gaps / commands and results).
Also write it to `research/T16/REPORT_371.md`.
