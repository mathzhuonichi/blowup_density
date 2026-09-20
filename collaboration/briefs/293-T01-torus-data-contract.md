# Lane 293-T01-torus-data-contract — register the first Section 3 contract `T01.torus_data` (the T10 data layer, `TorusDataAPI`, 10 fields)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) contract-registration worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/293-T01-torus-data-contract` (git branch `erenup/293-T01-torus-data-contract`, based on
`origin/erenup/integration-section3` **after** lanes 283/284/285/286/287 landed: `formalization/NSFormalization/Section3/T10/{PeriodicData,PhysicalBridge,DatumBasics,Parseval,Leray}.lean`
and the probe `research/T10/probes/api_on_canonical.lean`, whose `TorusDataAPI` is now fully proved field by field — see the four `*_closes.lean` probes in `research/T10/probes/`).
Read `CLAUDE.md` (contract import rules; the "结构体例外" paragraph; `ensure_ascii=False`; frozen V1/Tests are not edited — you only **add** files), the D01 precedent
`verification/Contracts/V1/HomogeneousNorm.lean` + `Bindings/HomogeneousNorm.lean` + `Tests/HomogeneousNorm.lean` and the registry entry `D01.homogeneous_norm` in `verification/contracts.json`,
`research/T10/Spec.lean` (docstrings), `research/T10/RECONCILIATION.md` §5 (lead amendment 1), `research/T10/CANONICAL.md`, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/placeholder `Prop` fields; do not modify existing `Contracts/V*`, `Tests/*`, or any `formalization/` module.
- `Contracts/*` import only `Mathlib`/`Lean`/`Init`/`Contracts.*` (+ the whitelist `CONTRACT_CANONICAL_MODULES` in `experiments/check_contracts.py`; `Paper1.TorusCube` is **not** on it —
  restate `torusLift`/`periodicFourierCoeff`/`PeriodicTorus`/`PeriodicFrequency`/`periodicTorusMeasure` verbatim in the contract and bridge them by `rfl`; the whitelist is policy, do not extend it).
- Every restated definition gets a `rfl` bridge theorem in `Bindings/` (`theorem foo_eq : Contracts.V1.foo = NSFormalization.Section3.T10.foo := rfl`, or the `∀ args, … = …` form when
  implicit arguments make the bare equality fail to elaborate — say which).

## Scope of this contract (decided by the lead)
Register only the **data layer** that `TorusDataAPI` refers to: `IsPeriodicSpatial`, `torusLift`, `periodicFourierCoeff`, `periodicFrequencyWeight`, `PeriodicScalarData`,
`PeriodicVectorData`, `realPeriodicSubmodule`, `PeriodicSobolev`, `periodicSobolevDataNorm`, `IsPeriodicDatum` (amended), `periodicSobolevENorm`, `meanT`, `constantPartT`,
`meanZeroPartT`, `meanDecompositionT`, `meanZeroPeriodicSobolev`, `IsMeanZeroT`, `periodicAngularFrequencySq`, `homogeneousDatumWeight`, `IsPeriodicHomogeneousDatum` (amended),
`periodicHomogeneousENorm`, `periodicDerivativeSymbol`, `IsSolenoidalPeriodicDatum`, `periodicLeray`, `IsPeriodicLerayDatum`, `IsPeriodicReweight` — i.e. everything in
`PeriodicData.lean` **up to and including** the reweight predicate, plus `IsPeriodicOn`. The solution-class part (`IsPeriodicSobolevPath`, `forceSobolevENormT`, `initialClassT`,
`MemForceT`/`forceClassT`, pressure gauge, `ClassicalSolutionT`, lifespan/breakdown/density, energy norms) is **deferred** to the T11 registration (it needs the structure-exception
fieldwise conversions; do not include it here). Say so in the contract's module docstring.

## Deliverables
1. `verification/Contracts/V1/TorusData.lean` (namespace `BlowupDensity.Contracts.V1`, same file layout/docstring style as `HomogeneousNorm.lean` and `Data.lean`): the restated
   definitions (token-for-token from `PeriodicData.lean`, with `Space`/`SpatialField`/`coordinateVector` taken from `Contracts.V1.Data` — import it) and
   `structure TorusDataAPI : Prop` with the ten fields **verbatim from `research/T10/probes/api_on_canonical.lean`** (order, quantifiers, hypotheses incl. amendment 1), each with the
   spec's docstring (paper lines, exact quantifier order, non-vacuity note).
2. `verification/Bindings/TorusData.lean`: the `rfl` bridges (one per restated definition; a `PeriodicSobolev s` bridge via the submodule), and
   `def torusData : Contracts.V1.TorusDataAPI := { datum_unique := …, … }` assembled from `NSFormalization.Section3.T10.{datum_unique, datum_real, parseval_forward, parseval_backward,
   torusLift_injective, torusLift_surjective, mean_decomposition, meanZero_datum, leray_exists_contraction, leray_projector}` (transport across the bridges by `rfl`/`show`; if a field
   needs more than definitional unfolding, prove the transport lemma in the binding file and say why).
3. `verification/Tests/TorusData.lean` (`checkedTorusData`, `run_cmd TestSupport.checkAxioms`, a conformance `example` restating one field against `Spec.lean`); `warningAsError` holds
   there — no `Formal.*` imports.
4. Registry entry `T01.torus_data` (`version: 1`, `parent_task: T01`, honest `scope` text naming the ten fields and the deferred solution-class part; `ensure_ascii=False, indent=2`,
   additions only) in `verification/contracts.json`; claim/update `collaboration/work_items.json` for `T01`/`T10` as the ledger tool allows (`python3 experiments/tasks.py claim T10 erenup`
   if the node exists in the ledger; then `python3 experiments/tasks.py render`) — if the ledger tool rejects the node, report the exact message and leave the ledger untouched.
5. Records `research/T10/ATTEMPTS_CONTRACT.md`, conformance `research/T10/axioms_contract.lean`; update `research/T10/COMPARISON.md` ("Registered: `T01.torus_data`").

## Gates (paste outputs)
`scripts/gates.sh` from the worktree root (`make check`, `make test`, `make test-mutations`); `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3`
(exit 0, `registered_contracts: 38`, `base_compatibility_checked: true`); `git diff --stat verification/contracts.json`.

## Report
Commit on your branch (`[293-T01] register T01.torus_data`); end with four parts (what is registered / files / gaps with error text / commands and results). Also write it to `research/T10/REPORT_293.md`.
