# Lane 427-T12-UREG-dedupe-register — T12: dedupe the `contDiff_dirDeriv` clash (GradientLSix vs GradientLambdaL3) and complete the `T01.mean_zero_calculus` registration

You are a Lean 4 (v4.34.0-rc2 + Mathlib) worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/427-T12-UREG-dedupe-register` (git branch `erenup/427-T12-UREG-dedupe-register`, based on lane 419's branch merged with
`origin/erenup/integration-section3`). Lane 419 (codex astra) left a scaffold: `verification/Contracts/V1/MeanZeroCalculus.lean` (compiles), a partial `Bindings/MeanZeroCalculus.lean`,
a stub `Tests/MeanZeroCalculus.lean`, a registry entry `T01.mean_zero_calculus` in `verification/contracts.json`, and records `research/T12/{ATTEMPTS_UREG.md,REPORT_419.md,axioms_ureg.lean}`.
It stopped because `Section3/T12/GradientLSix.lean` (lane 400) and `Section3/T12/GradientLambdaL3.lean` (lane 405) both declare `contDiff_dirDeriv` (and possibly other helpers — check with
`grep -n "^theorem\|^lemma\|^def" ` on both and diff the names) in namespace `NSFormalization.Section3.T12`, so any module importing both fails with a duplicate declaration.
Read `CLAUDE.md` (contract import rules, `rfl` bridges, `ensure_ascii=False, indent=2`, frozen V1 files — the new V1 file of this lane is not yet frozen), the original registration brief
`collaboration/briefs/419-T12-UREG-contract.md` (deliverables 1–5 and gates), `research/T12/Spec.lean:287-…`, `research/T12/probes/api_on_canonical.lean`, lane 419's files, and the top 40
lines of `logs/LESSONS.md`.

## Ground rules
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`/placeholder fields. **Lead-approved exception**: you may edit the two existing modules `GradientLSix.lean` and `GradientLambdaL3.lean` ONLY to
  remove the duplicated helper declarations and import them from a new shared module `formalization/NSFormalization/Section3/T12/DirDeriv.lean` (move the common helpers there verbatim —
  if the two copies differ, keep the more general one and prove the other from it; say exactly what differs). No statement of any exported theorem changes.
- Every restated definition in `Contracts/V1/MeanZeroCalculus.lean` must have a `rfl` bridge in `Bindings/`; every declaration prints exactly `[propext, Classical.choice, Quot.sound]`.

## Do
1. Dedupe: create `DirDeriv.lean`, rewire both modules, rebuild `lake build NSFormalization.Section3.T12.GradientLSix NSFormalization.Section3.T12.GradientLambdaL3
   NSFormalization.Section3.T12.CriticalL3Density NSFormalization.Section3.T20.CriticalTrilinear` (0 errors), and re-run the T12 probes/audits `research/T12/probes/gradient_l6_closes.lean`,
   `gradient_lambda_l3_closes.lean`, `research/T12/axioms_u5.lean`, `axioms_u6.lean` (all still green). Write one line in `logs/LESSONS.md` (two parallel lanes in one namespace can
   collide on helper names; the reviewer of the second lane should grep the first).
2. Complete the registration per the 419 brief: verify the contract file is token-for-token the Spec (fix if not), finish `Bindings/MeanZeroCalculus.lean` (all `rfl` bridges, the
   9-field instance from `velocityCriticalL3` (CriticalL3Density), `gradientLSix`, `gradientLambdaCriticalL3`, `boundedRepresentative`/`hTwo_le_laplacian`/`lambda_exists`, `tameProduct`,
   `spectralGap`-based fields, with the constants), `Tests/MeanZeroCalculus.lean` (`checkedMeanZeroCalculus`, `run_cmd TestSupport.checkAxioms`, conformance `example`, non-vacuity),
   registry entry (honest `scope`), `work_items.json` + `python3 experiments/tasks.py render`; records `research/T12/ATTEMPTS_UREG.md` (rewrite truthfully; keep 419's text under a
   "superseded" heading), `research/T12/axioms_ureg.lean`, T12 status in `T12_SPLIT.md`, `research/T12/REPORT_427.md` (or the full report in your message if the guard blocks it).

## Gates (paste outputs)
`scripts/gates.sh` from the worktree root (`make check`, `make test`, `make test-mutations`); `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3` (exit 0,
`registered_contracts: 43`, `base_compatibility_checked: true`); the axioms file; `git diff --stat verification/contracts.json`.

## Report
Commit on your branch (`[427-T12] …`); end with four parts (what changed incl. the exact dedupe / files / gaps / commands and results).
