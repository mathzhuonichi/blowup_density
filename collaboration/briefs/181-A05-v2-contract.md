# Lane 181-A05-v2-contract — register the critical embedding as A05 V2 (29th contract)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) contract-registration worker on the repository checked out at your
working directory `/data_8T/ping/blowup_density/.claude/worktrees/181-A05-v2-contract` (git branch
`erenup/181-A05-v2-contract`, based on branch `erenup/184-MAINT-merge-main` = `origin/erenup/integration` **plus** the merge of `origin/main`
(lane 184) — it contains lane 165's `Section4/A05/CriticalL3.lean`, lane 164's `Section4/D01/HomogeneousNorm.lean`
with the registered contract `D01.homogeneous_norm` (`Contracts/V1/HomogeneousNorm.lean`), and the owner's
C01 V4 `Contracts/V4/EnergyAbsorption.lean`). Read `CLAUDE.md` (contract import rules, `ensure_ascii=False`,
frozen V1 files), `collaboration/HANDOFF.md` §0, the top 40 lines of `logs/LESSONS.md`, then the A05 V1 trio
`verification/Contracts/V1/GradientL6.lean`, `verification/Bindings/GradientL6.lean`, `verification/Tests/GradientL6.lean`,
the registry entry `A05.gradient_l6`, the review `research/A05/REVIEW_165-A05-critical-l3.md` (which confirms
`A05.dotHomogeneousENorm = D01.dotHomogeneousENorm` by `rfl`), and `research/A05/Spec.lean:360-370`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/placeholder `Prop` fields; do not modify existing `Contracts/V*` or `Tests/*`.
  `Contracts/*` import only `Mathlib`/`Contracts.*` (+ whitelist in `experiments/check_contracts.py`); restated
  definitions bridged by `rfl` in `Bindings/`.

## Deliverables
1. `verification/Contracts/V2/GradientL6.lean`: `GradientL6V2API extends GradientL6API` adding the field
   `velocityCriticalL3` **token-for-token from `research/A05/Spec.lean:366-368`**, with the `Ḣ^{1/2}` norm
   spelled via the registered `Contracts.V1.HomogeneousNorm.dotHomogeneousENorm` (import it; do not restate a
   second copy) — if the spec's local def differs textually from the registered one, reconcile in the docstring
   and cite `REVIEW_165` §"canonical norm: rfl".
2. `verification/Bindings/GradientL6V2.lean`: `{ Bindings.gradientL6 with velocityCriticalL3 := … }` from
   `NSFormalization.Section4.A05.velocityCriticalL3` (`Section4/A05/CriticalL3.lean:394`), with the `rfl` bridge
   `A05.dotHomogeneousENorm = D01.dotHomogeneousENorm = Contracts….dotHomogeneousENorm` (compose the existing
   D01 bridge), the `MemHInfty` bridge if the contract's hypothesis is stated differently (say which), and
   `gradientL6_of_v2 := rfl`.
3. `verification/Tests/GradientL6V2.lean` (`checkedGradientL6V2`, `run_cmd TestSupport.checkAxioms`, a
   conformance `example` restating the field against `Spec.lean`).
4. Registry entry `A05.gradient_l6_v2` (`version: 2`, `parent_task: A05`, honest scope incl. the constant),
   `ensure_ascii=False, indent=2`, additions only; `work_items.json` + `python3 experiments/tasks.py render`.
5. Records `research/A05/ATTEMPTS_V2_CONTRACT.md`, conformance `research/A05/axioms_v2_contract.lean`; update
   `research/A05/COMPARISON.md` (registered V2).

## Gates (paste outputs)
`scripts/gates.sh` from the worktree root (`make check`, `make test`, `make test-mutations`);
`python3 experiments/check_contracts.py --base-ref origin/erenup/integration` (exit 0, `registered_contracts: 29`,
`base_compatibility_checked: true`); the axioms file; `git diff --stat verification/contracts.json`.

## Report
Commit on your branch; end with four parts. Also write it to `research/A05/REPORT_181.md`.
