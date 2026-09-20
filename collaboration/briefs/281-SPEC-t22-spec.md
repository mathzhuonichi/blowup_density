# Lane 281-SPEC-t22-spec — produce the reconciled specification of T22 (eq:zero-extension) on top of the reconciled T10 vocabulary

You are a Lean 4 (v4.34.0-rc2 + Mathlib) **specification** worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/281-SPEC-t22-spec` (git branch `erenup/281-SPEC-t22-spec`, based on `origin/erenup/integration-section3`, which now contains
`research/T10/Spec.lean` (the reconciled periodic data layer: `PeriodicSobolev s`, `IsPeriodicDatum`, `periodicSobolevENorm`, the homogeneous datum/norm, `meanT`/mean-zero, `torusLift`,
`periodicFourierCoeff`, …) and `research/T10/COMPARISON.md`). Read `CLAUDE.md` (contract rules), **the lead's decisions** `research/T22/RECONCILIATION.md` (binding), the two blind drafts
(`git show erenup/275-SPEC-t22-draft-a:research/T22/DraftA.lean`, `…:research/T22/COMPARISON_A.md`, `git show erenup/276-SPEC-t22-draft-b:research/T22/DraftB.lean`, `…:research/T22/COMPARISON_B.md`),
the paper `03-torus.tex:21-60` (eq:zero-extension and its proof), and T10's `Spec.lean` **which you must import/reuse** (`import` is not possible across `research/` files unless you put the
T10 definitions in scope — do it the way T10's own `Spec.lean` is structured: if it is a standalone file, `research/T22/Spec.lean` should start by `import`-ing the same modules and then
**re-use T10's names by reference**: the simplest robust way is to make `research/T22/Spec.lean` a file that `import`s nothing from `research/` but copies the *minimal* T10 definitions it needs
verbatim with a header comment `-- copied verbatim from research/T10/Spec.lean:<lines>; must stay identical until T01.torus_data is registered` — say which approach you used and why).

## Ground rules
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. No proofs; new files only.
- **Follow `research/T22/RECONCILIATION.md` exactly** (its §2 rulings and §3 decisions are binding; use the T10 vocabulary where the reconciliation says so, else the registered `Data.lean` vocabulary).

## Deliverables
1. `research/T22/DraftA.lean`, `DraftB.lean`, `COMPARISON_A.md`, `COMPARISON_B.md`, `REPORT_275.md`, `REPORT_276.md` copied verbatim from the two branches (provenance).
2. `research/T22/Spec.lean`: the reconciled statement — **elaborates** (`cd verification && lake env lean ../research/T22/Spec.lean`, 0 errors); docstrings cite `03-torus.tex:<line>`; a
   "non-vacuity" comment per field.
3. `research/T22/COMPARISON.md`: merged paper-clause → Lean field table with A/B provenance and the rulings; §"Proof dependencies" (from the reconciliation §4, refined with the exact T10
   lemmas needed — cross-reference `research/T10/COMPARISON.md`'s "needs a lemma" items); §"Open questions for the owner".
4. Report in four parts; write it to `research/T22/REPORT_278.md`; commit on your branch.
