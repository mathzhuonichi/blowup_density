# Lane 379-T13-contract — register the T13 uniform localization contract `T02.localization` v1 (42nd contract), on top of lane 359

You are a Lean 4 (v4.34.0-rc2 + Mathlib) contract-registration worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/379-T13-contract` (git branch `erenup/379-T13-contract`, based on lane 359's branch merged with `origin/erenup/integration-section3`:
`Section3/T13/{Localization,ConstantEndpoints,TorusIdentity,WholeSpaceIdentity,LocalizationKernel,KernelComparison,Assembly}.lean` with `localizationAPI : LocalizationAPI` (all six
fields) proved). Read `CLAUDE.md` (contract import rules, frozen `Contracts/V1`/`Tests`, `ensure_ascii=False`), the registered Section 3 contracts as templates — `Contracts/V1/LocalPotential.lean`
+ `Bindings/LocalPotential.lean` + `Tests/LocalPotential.lean` (lane 371, #337) and `Contracts/V1/TorusData.lean` (+ bindings/tests; lane 275) — the registry entries
`T01.torus_data`, `T02.local_potential` in `verification/contracts.json` (scope wording), then **`research/T13/Spec.lean`** (the reconciled statement, token-for-token source:
`fundamentalCube`, `SupportedInBall`, `periodize`, `fractionalRadialKernel`, `cFrac`, `periodicKernel`, `latticeTail`, `IReal`, `ITorus`, the endpoint quantities, `structure LocalizationAPI : Prop`
with six fields), `research/T13/probes/api_on_canonical.lean` and `research/T13/probes/assembly_closes.lean` (how the Spec's record closes from `localizationAPI`),
`research/T13/{RECONCILIATION.md,COMPARISON.md,REPORT_359.md}`, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/placeholder `Prop` fields; do not modify existing `Contracts/V*`, `Tests/*`, `formalization/` modules. `Contracts/*` import only
  `Mathlib`/`Lean`/`Init`/`Contracts.*` (+ the whitelist in `experiments/check_contracts.py`); every restated `def` gets an `rfl` bridge in `Bindings/`; the `dotHomogeneousENorm` of the
  whole-space side is the registered `Contracts.V1.HomogeneousNorm.dotHomogeneousENorm` (import it; bridge `rfl` as `Bindings/GradientL6V2.lean:44` does). `Tests/` is `warningAsError`.
- No goal repackaging: the registered `declaration` must be the transported `localizationAPI`, not a hypothesis.

## Deliverables
1. `verification/Contracts/V1/Localization.lean` (namespace `BlowupDensity.Contracts.V1`, `import Contracts.V1.TorusData`, `Contracts.V1.HomogeneousNorm`): restate **token-for-token from
   `research/T13/Spec.lean`** the T13 vocabulary and `structure LocalizationAPI : Prop` (six fields: `constant_pos_finite`, `wholeSpace_identity`, `torus_identity`, `localization`,
   `endpoint_zero`, `endpoint_one`, with docstrings and paper lines `03-torus.tex:22-98`).
2. `verification/Bindings/Localization.lean`: `rfl` bridges for every restated `def` (`fundamentalCube_eq`, `periodize_eq`, `cFrac_eq`, `IReal_eq`, `ITorus_eq`, …; pointwise if needed — say
   which), and `theorem localizationAPI : Contracts.V1.LocalizationAPI` from `NSFormalization.Section3.T13.localizationAPI` (fieldwise through the bridges; the structure is `Prop`-valued so a
   direct term is fine).
3. `verification/Tests/Localization.lean`: `checkedLocalization`, `run_cmd TestSupport.checkAxioms`, a Spec conformance `example` per field, and a non-vacuity `example` (the `localization`
   field instantiated at `s = 1/2` on a nonzero `ContDiffBump` field as in `research/T13/probes/assembly_closes.lean` — restate the witness in the test through `Bindings`).
4. Registry entry `T02.localization` (`parent_task: "T02"`, `version: 1`, shape of `T02.local_potential`; honest `scope`: the two Gagliardo identities with the explicit constant `cFrac`,
   the endpoint identities, the uniform localization estimate with the explicit constant `(1 + (4·tailGeomConst/cFrac)^{1/2}).toReal`, all for `0 < s < 1`), `ensure_ascii=False, indent=2`,
   additions only. Ledger: `python3 experiments/tasks.py claim T13 erenup && python3 experiments/tasks.py render`, add `T02.localization` to T13's `contracts` in
   `collaboration/work_items.json`, render again, `make check`.
5. Records: `research/T13/ATTEMPTS_CONTRACT.md`, conformance `research/T13/axioms_contract.lean`, `research/T13/COMPARISON.md` §"Registered", report `research/T13/REPORT_379.md`.

## Gates (paste outputs)
`scripts/gates.sh` from the worktree root with `BASE_REF=origin/erenup/integration-section3` (`make check`, `make test`, `make test-mutations`);
`python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3` (exit 0, `registered_contracts: 42`, `base_compatibility_checked: true`);
the axioms file; `git diff --stat verification/contracts.json` (additions only).

## Report
Commit on your branch (separate commits for the ledger claim and the contract); end with four parts. Also write it to `research/T13/REPORT_379.md`.
