# Lane 296-MAINT-t10-instance-dedupe — name the torus-measure instances once, restore the direct four-module binding of `T01.torus_data`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) maintenance worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/296-MAINT-t10-instance-dedupe` (git branch `erenup/296-MAINT-t10-instance-dedupe`, based on `origin/erenup/integration-section3`
**after** lane 293 landed: `verification/Contracts/V1/TorusData.lean`, `Bindings/TorusData.lean`, `Tests/TorusData.lean`, registry entry `T01.torus_data`).
Read `CLAUDE.md` (Lean environment; contract rules — you must **not** change `Contracts/V1/TorusData.lean` or `Tests/TorusData.lean`), `research/T10/REPORT_293.md` §3
and `research/T10/ATTEMPTS_CONTRACT.md` (the exact import-clash errors), the top 40 lines of `logs/LESSONS.md` (the 2026-09-17 instance-name lesson), and the four proof
modules `formalization/NSFormalization/Section3/T10/{PhysicalBridge,DatumBasics,Parseval,Leray}.lean` plus `PeriodicData.lean`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`. This lane is **allowed** (lead decision) to edit the four T10 proof modules and `Bindings/TorusData.lean`, and to add one
  declaration to `PeriodicData.lean`; it must **not** change any definition's statement/body in `PeriodicData.lean` (the contract restates them by `rfl`), any theorem
  statement in the proof modules, `Contracts/*`, `Tests/*`, or `contracts.json`.

## Task
1. Root cause: anonymous `instance : IsProbabilityMeasure (volume : Measure UnitAddCircle)` (and any other anonymous instances / `local instance` helpers) are declared
   separately in `Parseval.lean`, `DatumBasics.lean`, `PhysicalBridge.lean` and receive the same generated name. Fix: declare each shared instance **once, with an
   explicit name**, in `PeriodicData.lean` (e.g. `instance unitAddCircle_volume_isProbabilityMeasure : …` and `instance periodicTorusMeasure_isProbabilityMeasure : IsProbabilityMeasure periodicTorusMeasure`),
   delete the duplicates from the three proof modules (keep any module-specific helper but give it a unique explicit name), and verify **all four proof modules import together**:
   a probe `research/T10/probes/all_four_import.lean` importing the four modules must elaborate with no output.
2. Rewrite `verification/Bindings/TorusData.lean` to import all four proof modules and assemble `torusData` **directly** from the ten named theorems
   (`NSFormalization.Section3.T10.{torusLift_injective, torusLift_surjective, mean_decomposition, datum_unique, datum_real, meanZero_datum, parseval_forward, parseval_backward,
   leray_exists_contraction, leray_projector}`), deleting the private re-proofs lane 293 had to add; keep every `rfl` bridge theorem exactly as it is (same names/statements).
   `Tests/TorusData.lean` stays byte-identical and must still pass.
3. Records: `research/T10/ATTEMPTS_DEDUPE.md`; update `research/T10/REPORT_293.md`? No — do not edit other lanes' reports; write `research/T10/REPORT_296.md`.

## Gates (paste outputs)
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T10.PeriodicData NSFormalization.Section3.T10.PhysicalBridge NSFormalization.Section3.T10.DatumBasics NSFormalization.Section3.T10.Parseval NSFormalization.Section3.T10.Leray`
(0 errors), `lake env lean` on the four-module probe and on every `research/T10/probes/*_closes.lean` (0 output — the field probes must still close), `scripts/gates.sh` from the worktree
root (`make check`, `make test`, `make test-mutations`), `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3` (exit 0, `registered_contracts: 38`,
`base_compatibility_checked: true`), `git diff --stat` (must show no change to `Contracts/`, `Tests/`, `contracts.json`, and no statement changes in the proof modules — show the diff of each proof module).

## Report
Commit on your branch (`[296-MAINT] name T10 torus-measure instances once; direct four-module binding`); end with four parts (what changed / files / gaps with error text / commands and results).

## Also fold in the review notes of lane 293 (`research/T01/REVIEW_293-T01-torus-data-contract.md` §3)
- `Bindings/TorusData.lean`: `torusData` is a `Prop`-valued declaration → make it `theorem torusData : … := …` (or keep `def` with `set_option linter.defProp false in` immediately before it and say why); the registry's `declaration` stays `BlowupDensity.Tests.checkedTorusData` (unchanged).
- `research/T10/axioms_contract.lean`: remove the zero-axiom `#print axioms periodicFrequency_eq` line (or label it as a definitional check), keeping the ten field-level `#print axioms`.
- Correct the one-line binding docstring the review calls inaccurate (it must describe the direct four-module assembly after your rewrite).
