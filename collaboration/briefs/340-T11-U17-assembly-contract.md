# Lane 340-T11-U17-assembly-contract — assemble the four T11 APIs and register the contract `T01.torus_local_theory` (lead amendment 2: H³-ball continuation, H¹ statements kept as named manuscript predicates)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) contract worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/340-T11-U17-assembly-contract` (git branch `erenup/340-T11-U17-assembly-contract`, based on `origin/erenup/integration-section3` after every T11 unit landed).
Read `CLAUDE.md` (contract import rules; the "结构体例外" paragraph; frozen V1/Tests; `ensure_ascii=False`), the T10 precedent `verification/Contracts/V1/TorusData.lean` + `Bindings/TorusData.lean` +
`Tests/TorusData.lean` (lanes 293/296) and the Section 4 precedent for a narrowed continuation API `verification/Contracts/V2/Continuation.lean` (`RestartFixedForce`, `ManuscriptHorizonLowerBoundH1`
in `Contracts/V2/LocalTheory.lean` — how a manuscript statement is kept as a named unproved predicate next to the proved narrowing), `research/T11/Spec.lean`, `research/T11/RECONCILIATION.md`,
`research/T11/LEAD_AMENDMENTS.md` (amendments 1 and 2 — **binding**), `research/T11/H1_GAP.md` (lane 338), `research/T11/T11_SPLIT.md` §1 status lines (which module proves which field:
`Uniqueness.lean` (U5), `Maximal.lean` + `ExtendsBeyond.lean` (U15/U14/U16, with the `_of_input` bridges), `Restart.lean` + `ExistenceInputH3.lean` (U10/U11/U9e: `restartH3`, `periodicLocalTheoryAPI_of_input`,
`periodicQuantitativeLocalInputH3`), `PairingBound.lean` (`torusHigherOrderBound`), `RestartBeyond.lean`, `MeanIdentity.lean` (U7), `GalileanClasses.lean` (U3), `Rescaling.lean` (U4), `Transport.lean` +
`ClassicalRegularity.lean` (U6/U6b), `MildClassical.lean`), the probe `research/T11/probes/api_on_canonical.lean` (the target structures), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/placeholder `Prop` fields; do not modify existing `Contracts/V*`, `Tests/*`, `formalization/` modules; `Contracts/*` import only `Mathlib`/`Contracts.*` (+ whitelist);
  every restated definition bridged by `rfl` in `Bindings/` — **except** `ClassicalSolutionT` (structure exception: fieldwise conversions `toContract`/`ofContract` with round trips; the single local
  restatement is `Section3/T10/PeriodicData.lean`).

## Deliverables
1. `formalization/NSFormalization/Section3/T11/Assembly.lean`: the four API terms over the canonical modules — `def periodicLocalTheoryAPI : PeriodicLocalTheoryAPI` (8 fields: `horizon`/`solution`/
   `regularity` from `Restart.lean`'s package instantiated with `periodicQuantitativeLocalInputH3` (338) and `ClassicalRegularity.lean`; `velocity_unique`/`pressure_unique`/`horizon_le_lifespan` (315);
   `exists_maximal`/`maximal_unique` (323 via 337/338's bridges)), `theorem periodicMeanReductionAPI : PeriodicMeanReductionAPI` (316 + 310 + 331/339), `theorem periodicViscosityRescalingAPI :
   PeriodicViscosityRescalingAPI` (314 + 331/339), and the **H³-narrowed** continuation API `structure PeriodicContinuationH3API : Prop` (the spec's `PeriodicContinuationAPI` with the `H¹` ball of `restart`
   and `restartBeyond` replaced by the `H³` ball, everything else verbatim) with `theorem periodicContinuationH3API : PeriodicContinuationH3API` (338's `restartH3`/`restartBeyondH3`/`extendsBeyondH3`/
   `lifespanInfiniteOfLocallyFiniteH3`, 336's `torusHigherOrderBound`). Also `def PeriodicRestartH1 : Prop` and `def PeriodicRestartBeyondH1 : Prop` = the spec's `H¹`-ball fields verbatim (named, documented
   as the manuscript's statements, **not proved**), and `theorem periodicContinuationAPI_of_h1 (h₁ : PeriodicRestartH1) (h₂ : PeriodicRestartBeyondH1) : PeriodicContinuationAPI` (the V1 API follows from the
   two named predicates plus the proved fields — this exhibits exactly what is missing). Probe `research/T11/probes/assembly_closes.lean`: every spec field closed by name.
2. `verification/Contracts/V1/TorusLocalTheory.lean` (namespace `BlowupDensity.Contracts.V1`, importing `Contracts.V1.TorusData`): restate token-for-token the deferred T10 solution-class declarations
   (`IsPeriodicSobolevPath`, `forceSobolevENormT`, `initialClassT`, `MemForceT`/`forceClassT`, `pressureMeanT`/`PressureGaugeT`/`normalizePressureT`, `ClassicalSolutionT` (contract copy), `maximalLifespanT`,
   `RegularThroughT`, `breakdownSetInT`/`breakdownSetT`, `RelativelyDenseT`, the energy norms) and the T11 vocabulary (`IsPeriodicSobolevPathOn`, `convectionDivergenceT`, `scalarSpatialLaplacianT`, `SolvesBelowT`,
   `IsMaximalPeriodicSolution`, `squaredHTwoIntegralT`, `timeShiftT`, `ExtendsBeyondT`, `galileanMeanT` and transforms, the rescaling maps), `PeriodicLocalRegularity`, the four API structures (with
   `PeriodicContinuationH3API` and the two named `H¹` predicates), each with the spec's docstrings and an explicit "registered narrowing" note on the continuation API.
3. `verification/Bindings/TorusLocalTheory.lean`: `rfl` bridges for every restated `def`; for `ClassicalSolutionT` the fieldwise conversions + round-trip lemmas (field types defeq); transport of the four
   API terms across the conversions (`torusLocalTheoryAPI`, `torusContinuationH3API`, `torusMeanReductionAPI`, `torusViscosityRescalingAPI`); `verification/Tests/TorusLocalTheory.lean` with
   `checkedTorusLocalTheory` bundling the four terms, `run_cmd TestSupport.checkAxioms`, a conformance `example` per API restated against `Spec.lean`.
4. Registry entry `T01.torus_local_theory` (`version: 1`, `parent_task: T01`, honest `scope`: what is proved, the `H³` narrowing, the two named `H¹` predicates and `H1_GAP.md`), `ensure_ascii=False, indent=2`,
   additions only; `python3 experiments/tasks.py claim T11 erenup && python3 experiments/tasks.py render` if the ledger accepts the node (else report). Records: `research/T11/ATTEMPTS_ASSEMBLY.md`,
   `research/T11/axioms_assembly.lean`, `research/T11/REPORT_340.md`, and `research/T11/COMPARISON.md` §"Registered".

## Gates (paste outputs)
`scripts/gates.sh` from the worktree root (`make check`, `make test`, `make test-mutations`); `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3`
(exit 0, `registered_contracts: 39`, `base_compatibility_checked: true`); the axioms file; `git diff --stat verification/contracts.json`.

## Report
Commit on your branch (`[340-T11] register T01.torus_local_theory`); end with four parts (what is registered / files / gaps — the two named `H¹` predicates and the consumer checklist / commands and results).
