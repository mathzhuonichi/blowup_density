# Lane 378-SPEC-t19-spec — produce the reconciled specification of T19 (the density package: `prop:density`, `cor:mixed`, `cor:closure`, `prop:projection`) from the lead's reconciliation of the two blind drafts

You are a Lean 4 (v4.34.0-rc2 + Mathlib) **specification** worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/378-SPEC-t19-spec` (git branch `erenup/378-SPEC-t19-spec`, based on `origin/erenup/integration-section3` **after** the commit
"T19 reconciliation (Opus draft, lead-approved)", so `research/T19/RECONCILIATION.md` is on your base — verify with `ls research/T19/`). Read `CLAUDE.md` (contract import rules; no
placeholder `Prop`s; docstrings cite paper lines), then **the lead's decisions `research/T19/RECONCILIATION.md` (binding: §2 rulings, §3 decisions incl. the field roster and citation
hygiene, §"False clauses / traps")**, the two blind drafts (not on your base; read them with `git show erenup/367-SPEC-t19-draft-a:research/T19/DraftA.lean`,
`git show erenup/367-SPEC-t19-draft-a:research/T19/COMPARISON_A.md`, `git show erenup/372-SPEC-t19-draft-b:research/T19/DraftB.lean`, `git show erenup/372-SPEC-t19-draft-b:research/T19/COMPARISON_B.md`),
the paper `paper/sections/03-torus.tex:349-382,528-631` (re-cite the projection remarks at the current lines `:579/:586/:590/:591`), the registered vocabulary
`verification/Contracts/V1/{TorusData,TorusLocalTheory,MainThresholds,CompletedDensity,Data,MaximalPartial,Correction}.lean` (import and use by name; nothing registered is copied),
and `research/T18/Spec.lean:395-442` (the unregistered `IsPeriodicLebesgueSlicePath` / `mixedLebesgueENormT` to copy verbatim in the historical namespace, per §3).

## Ground rules
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. No proofs, no edits to existing modules; new files only.
- **Follow the reconciliation's decisions exactly** (bases B/B/A/A; all four `Prop`; T18 record not threaded; `RelativelyDenseT`/`RelativelyDenseMixedT`; registered `alpha`; no honesty
  guards; `𝓧` topology by fixing `a`; the exact field roster of §3; drop everything §3 drops). Where the reconciliation says "verify", verify with an `example … := rfl` in the spec file and report.

## Anti-stub clause
Every field must be a concrete clause of the paper's result in the registered vocabulary: no `True`, no `∃ x, True`, no tautologies, no definitions ignoring their arguments, no
self-made stubs for the imported records. Before reporting, print `grep -nE ': *True|:= *0$|→ *True' research/T19/Spec.lean` and confirm it is empty.

## Deliverables
1. `research/T19/DraftA.lean`, `DraftB.lean`, `COMPARISON_A.md`, `COMPARISON_B.md`, `REPORT_367.md`, `REPORT_372.md` copied verbatim from the two branches (provenance).
2. `research/T19/Spec.lean`: the reconciled statement — the four `Prop` structures `PeriodicDensityAPI` (3), `MixedRegionAPI` (3), `StrongClosureAPI` (4), `ProjectionAPI` (3) in namespace
   `BlowupDensity.T19` with every field's docstring citing `03-torus.tex:<line>` (current line numbers), the exact quantifier order and a "non-vacuity" note, the helper definitions
   the roster names (`RelativelyDenseMixedT`, `RegularTrajectoryT`/`SingularTrajectoryT`, `extendedBreakdownSetT`, `spaceTimeL2L2ENormT`, …), and the four `def …Statement : Prop` in the
   paper's quantifier order; **elaborates** (`cd verification && lake env lean ../research/T19/Spec.lean`, 0 errors).
3. `research/T19/COMPARISON.md`: merged paper-clause → Lean field table with A/B provenance, the R41/R46 counterpart field, and the reconciliation's rulings; §"Proof dependencies"
   copied from the reconciliation §4 (which T11/T18 fields each proof consumes); §"Open questions for the owner" (the five of the reconciliation).
4. Report in four parts (what was stated with field counts / files / deviations from the reconciliation with reasons / commands and results); write it to `research/T19/REPORT_378.md`
   (if a guard blocks the write, put the full report in your final message); commit on your branch.
