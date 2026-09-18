# Lane 420-T24-Uc3-conservative-registration — T24c Uc3: assemble `ConservativeForcingAPI` and register `T04.conservative_forcing`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) contract-registration worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/420-T24-Uc3-conservative-registration` (git branch `erenup/420-T24-Uc3-conservative-registration`, based on `origin/erenup/integration-section3`,
which contains `Section3/T24/Conservative.lean` (Uc1: `PeriodicPotentialT`, `conservativeForceT`, `zero_from_rest`) and `Section3/T24/PotentialPairing.lean` (Uc2: `potential_pairing`)).
Read `CLAUDE.md` (contract import rules, structure exception for `ClassicalSolutionT` as in `T01.torus_local_theory`, `ensure_ascii=False, indent=2`), `research/T24/T24_SPLIT.md` §0 and
unit **Uc3** (`:90-94`), `research/T24/Spec.lean:1360-1420` (`ConservativeForcingAPI`, 2 fields, and `conservativeForcingStatement :1416`), `research/T24/REVIEW_395-T24-Uc2-potential-pairing.md`
(note: a genuine `ClassicalSolutionT` non-vacuity witness is required — the rest solution at `φ = 0`), the registration precedents `verification/Contracts/V1/TorusLocalTheory.lean`,
`Bindings/TorusLocalTheory.lean`, `Tests/TorusLocalTheory.lean` (structure exception + fieldwise conversions), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`/placeholder `Prop` fields; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only (except the registry/work-items additions named below).
- No named inputs. Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line.

## Deliverables
1. `formalization/NSFormalization/Section3/T24/ConservativeAssembly.lean`: the canonical 2-field record assembled from Uc1/Uc2 (`zero_from_rest`, `potential_pairing`) and the statement
   alias, over the canonical T10/T11 vocabulary; plus the rest-solution witness `ClassicalSolutionT ν 0 (conservativeForceT 0) T` (zero velocity, zero pressure; `conservativeForceT 0 = 0`) —
   grep first for an existing zero `ClassicalSolutionT` in `Section3/T11` or T24 probes and reuse it.
2. `verification/Contracts/V1/ConservativeForcing.lean`: `ConservativeForcingAPI` token-for-token from `Spec.lean` over the registered `Contracts/V1/TorusLocalTheory.lean` vocabulary
   (`ClassicalSolutionT`, `periodicTorusMeasure`, `torusLift`, `pressureGradient`, …; restate only what is unregistered, with provenance comments), `conservativeForcingStatement`.
3. `verification/Bindings/ConservativeForcing.lean`: `rfl` bridges / fieldwise conversions (`ClassicalSolutionT` structure exception: use the existing conversions in
   `Bindings/TorusLocalTheory.lean`), the instance `conservativeForcing : ConservativeForcingAPI`, `conservativeForcingStatement_holds`.
4. `verification/Tests/ConservativeForcing.lean`: `checkedConservativeForcing`, `run_cmd TestSupport.checkAxioms`, conformance `example`, non-vacuity via the rest solution.
5. Registry entry `T04.conservative_forcing` (`version: 1`, honest `scope` recording the bounded-domain/no-slip omission as out of V1 scope), `work_items.json` + `tasks.py render`;
   records `research/T24/ATTEMPTS_UC3.md`, `research/T24/axioms_uc3.lean`, Uc3 status in `T24_SPLIT.md`.

## Gates (paste outputs)
`scripts/gates.sh` from the worktree root; `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3` (exit 0, `registered_contracts` one more than the base,
`base_compatibility_checked: true`); the axioms file; `git diff --stat verification/contracts.json`.

## Report
Commit on your branch; end with four parts. Also write it to `research/T24/REPORT_420.md`.
