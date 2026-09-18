# Lane 419-T12-UREG-contract — register T12 `MeanZeroSobolevCalculusAPI` (9 fields, all proved) as contract `T01.mean_zero_calculus` (43rd contract)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) contract-registration worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/419-T12-UREG-contract` (git branch `erenup/419-T12-UREG-contract`, based on `origin/erenup/integration-section3`). Read `CLAUDE.md`
(contract import rules: `Contracts/*` import only `Mathlib`/`Contracts.*` + the whitelist in `experiments/check_contracts.py`; restated definitions bridged by `rfl` in `Bindings/`;
structure exception for `ClassicalSolutionT`; `ensure_ascii=False, indent=2`; frozen V1 files untouched), the T12 spec `research/T12/Spec.lean:287-…` (`MeanZeroSobolevCalculusAPI`,
9 fields, and the statement def), the canonical restatement probe `research/T12/probes/api_on_canonical.lean` (the 9 fields over `Section3/T12/MeanZeroCalculus.lean` vocabulary),
`research/T12/T12_SPLIT.md` (all 9 units DONE: U1 HaarCube, U2 Cutoff, U3 CutoffGagliardo, U4 CriticalL3 + CriticalL3Density (`velocityCriticalL3`), U5 GradientLSix
(`gradientLSix`, `Csix`), U6 GradientLambdaL3 (`gradientLambdaCriticalL3`, `CcriticalThreeHalves`), plus `SpectralGap`, `FourierEmbeddings`
(`boundedRepresentative`/`hTwo_le_laplacian`/`lambda_exists`), `TameProduct`), the registration precedents `verification/Contracts/V1/Localization.lean`,
`Bindings/Localization.lean`, `Tests/Localization.lean` (lane 371, contract `T02.localization`) and `Contracts/V1/TorusLocalTheory.lean`/`Bindings/TorusLocalTheory.lean`
(lane 340; how registered T10/T11 vocabulary is consumed by import), the registry `verification/contracts.json`, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`/placeholder `Prop` fields; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only (except the registry/work-items additions named below).
- No named inputs. Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line.

## Deliverables
1. `verification/Contracts/V1/MeanZeroCalculus.lean`: `MeanZeroSobolevCalculusAPI` **token-for-token from `research/T12/Spec.lean`** (all 9 fields + constants, docstrings citing
   paper lines), importing the registered `Contracts/V1/TorusData.lean` vocabulary and restating verbatim (with provenance comments) only what is not registered
   (`periodicLpENorm`, `periodicHomogeneousENorm`, `MemPeriodicHomogeneous`, `IsMeanZeroT`, `SmoothPeriodicT`, `gradientTensor`, `laplacian`, `IsPeriodicLambda`, … — read what
   `Spec.lean` uses); `def meanZeroCalculusStatement : Prop := Nonempty MeanZeroSobolevCalculusAPI` (or the Spec's own statement def, verbatim).
2. `verification/Bindings/MeanZeroCalculus.lean`: `rfl` bridges from every restated definition to the canonical `NSFormalization.Section3.T12.*` one (each restated def must have a
   bridge; if a canonical def is not `rfl`-equal, write the fieldwise conversion and say why), then the instance `meanZeroCalculus : MeanZeroSobolevCalculusAPI` assembled from the
   9 proved theorems (`Csix`, `CcriticalHalf`, `CcriticalThreeHalves`, `gapConst`/`hTwoConst` etc. as the constants), and `theorem meanZeroCalculusStatement_holds`.
3. `verification/Tests/MeanZeroCalculus.lean`: `checkedMeanZeroCalculus`, `run_cmd TestSupport.checkAxioms` (standard three), a conformance `example` restating one field against
   `Spec.lean`, and a non-vacuity example (the nonzero mean-zero witness `meanZeroPartT (x ↦ cos(2π x₀)·e₀)` used by the T12 probes).
4. Registry entry `T01.mean_zero_calculus` in `verification/contracts.json` (`version: 1`, `parent_task`, honest `scope` incl. that the constants are closed terms, not numerals),
   `ensure_ascii=False, indent=2`, additions only; `collaboration/work_items.json` + `python3 experiments/tasks.py render`.
5. Records: `research/T12/ATTEMPTS_UREG.md`, conformance `research/T12/axioms_ureg.lean`; update `research/T12/T12_SPLIT.md` (registered) and the T12 line of `research/T12/COMPARISON.md` if present.

## Gates (paste outputs)
`scripts/gates.sh` from the worktree root (`make check`, `make test`, `make test-mutations`); `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3`
(exit 0, `registered_contracts: 43`, `base_compatibility_checked: true`); the axioms file; `git diff --stat verification/contracts.json`.

## Report
Commit on your branch; end with four parts. Also write it to `research/T12/REPORT_419.md`.
