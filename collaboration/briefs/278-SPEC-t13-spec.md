# Lane 278-SPEC-t13-spec — produce the reconciled specification of T13 (lem:localization) on top of the reconciled T10 vocabulary

You are a Lean 4 (v4.34.0-rc2 + Mathlib) **specification** worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/278-SPEC-t13-spec` (git branch `erenup/278-SPEC-t13-spec`, based on `origin/erenup/integration-section3`, which now contains
`research/T10/Spec.lean` (the reconciled periodic data layer: `PeriodicSobolev s`, `IsPeriodicDatum`, `periodicSobolevENorm`, the homogeneous datum/norm, `meanT`/mean-zero, `torusLift`,
`periodicFourierCoeff`, …) and `research/T10/COMPARISON.md`). Read `CLAUDE.md` (contract rules), **the lead's decisions** `research/T13/RECONCILIATION.md` (binding), the two blind drafts
(`git show erenup/265-SPEC-t13-draft-a:research/T13/DraftA.lean`, `…:research/T13/COMPARISON_A.md`, `git show erenup/266-SPEC-t13-draft-b:research/T13/DraftB.lean`, `…:research/T13/COMPARISON_B.md`),
the paper `03-torus.tex:21-60` (lem:localization and its proof), and T10's `Spec.lean` **which you must import/reuse** (`import` is not possible across `research/` files unless you put the
T10 definitions in scope — do it the way T10's own `Spec.lean` is structured: if it is a standalone file, `research/T13/Spec.lean` should start by `import`-ing the same modules and then
**re-use T10's names by reference**: the simplest robust way is to make `research/T13/Spec.lean` a file that `import`s nothing from `research/` but copies the *minimal* T10 definitions it needs
verbatim with a header comment `-- copied verbatim from research/T10/Spec.lean:<lines>; must stay identical until T01.torus_data is registered` — say which approach you used and why).

## Ground rules
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. No proofs; new files only.
- **Follow `research/T13/RECONCILIATION.md` exactly** (fixed fundamental cube; `periodize` as a def; API fields `constant_pos_finite`, `wholeSpace_identity`, `torus_identity`, `localization`,
  `endpoint_zero`, `endpoint_one`; the tail lemmas are not fields; `0 < s < 1`; vector fields; ℝ³ side uses the registered `dotHomogeneousENorm` and `eLpNorm f 2 volume`; torus side uses
  T10's `periodicSobolevENorm`/`periodicHomogeneousENorm`).

## Deliverables
1. `research/T13/DraftA.lean`, `DraftB.lean`, `COMPARISON_A.md`, `COMPARISON_B.md`, `REPORT_265.md`, `REPORT_266.md` copied verbatim from the two branches (provenance).
2. `research/T13/Spec.lean`: the reconciled statement — **elaborates** (`cd verification && lake env lean ../research/T13/Spec.lean`, 0 errors); docstrings cite `03-torus.tex:<line>`; a
   "non-vacuity" comment per field.
3. `research/T13/COMPARISON.md`: merged paper-clause → Lean field table with A/B provenance and the rulings; §"Proof dependencies" (from the reconciliation §4, refined with the exact T10
   lemmas needed — cross-reference `research/T10/COMPARISON.md`'s "needs a lemma" items); §"Open questions for the owner".
4. Report in four parts; write it to `research/T13/REPORT_278.md`; commit on your branch.
