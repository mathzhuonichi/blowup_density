# Lane 412-MAINT-t17-forceprofile-merge-repair — verify the restored `Section3/T17/ForceProfile.lean` builds with its whole T17 closure and probes

You are a Lean 4 (v4.34.0-rc2 + Mathlib) maintenance worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/412-MAINT-t17-forceprofile-merge-repair` (git branch `erenup/412-MAINT-t17-forceprofile-merge-repair`).
Context: PR #366 (lane 394) merged `origin/erenup/integration-section3` with a text-level conflict in `formalization/NSFormalization/Section3/T17/ForceProfile.lean` that the lead's
union-of-hunks resolver (meant for appended markdown notes) concatenated, producing duplicated imports, a duplicated module docstring and a docstring split by a stray `-/`
(a parse error). The lead has already replaced the file in this worktree by the reviewed lane-394 version (`git checkout c4be85b0 -- …ForceProfile.lean`, the commit at the tip of
this branch). Your job is verification and, only if needed, a minimal repair.

## Ground rules
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- Do not change any statement. If the restored file fails to build because a later lane changed a dependency, fix only what is needed (say exactly what) — no `sorry`/`admit`/`axiom`.

## Do
1. `git show HEAD --stat`, then `git diff HEAD~1 HEAD -- formalization/NSFormalization/Section3/T17/ForceProfile.lean | head` to see the restoration; confirm the file has no duplicate
   `import` lines and no unbalanced doc comments (`grep -c '^import' …`, `lake env lean` below).
2. Build the full T17 closure: `lake build NSFormalization.Section3.T17.ForceProfile NSFormalization.Section3.T17.Correction NSFormalization.Section3.T17.Transport
   NSFormalization.Section3.T17.CorrectionDeriv NSFormalization.Section3.T17.ForceDeriv NSFormalization.Section3.T17.LatticeDeriv NSFormalization.Section3.T17.CorrectionProfile` (0 errors),
   `lake env lean` on `ForceProfile.lean` (0 output), and on every T17 probe: `research/T17/probes/correction_canonical.lean`, `research/T17/probes/force_profile_canonical.lean`,
   `research/T17/probes/rev394_field_conformance.lean`, `research/T17/probes/rev394_mutation.lean` (this one is expected to FAIL — say so), `research/T17/probes/rev394_nonvacuity.lean`,
   and any other `research/T17/probes/*.lean` / `research/T17/axioms_*.lean` that import `ForceProfile` (grep). Also `grep -rln "T17.ForceProfile" formalization verification research`
   and build every importer.
3. `make check` from the worktree root; `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3` (`registered_contracts: 42`, `base_compatibility_checked: true`).
4. Write `research/MAINT/REPORT_412.md` (four parts: what was restored and verified / files / any residual with exact error text / commands and results) and commit
   `[412-MAINT] Verify restored ForceProfile.lean (T17 closure + probes)`.
