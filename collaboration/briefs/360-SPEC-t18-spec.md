# Lane 360-SPEC-t18-spec — produce the reconciled specification of T18 (`thm:insertion`, exact local insertion on the torus) from the lead's reconciliation of the two blind drafts

You are a Lean 4 (v4.34.0-rc2 + Mathlib) **specification** worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/360-SPEC-t18-spec` (git branch `erenup/360-SPEC-t18-spec`, based on `origin/erenup/integration-section3` **after** the
commit "T18 reconciliation (Opus draft, lead-approved)", so `research/T18/RECONCILIATION.md` is on your base — verify with `ls research/T18/`). Read `CLAUDE.md` (contract
import rules; no placeholder `Prop`s; docstrings cite paper lines), then **the lead's decisions `research/T18/RECONCILIATION.md` (binding: §2 rulings, §3 decisions, §"False
clauses / traps")**, and the two blind drafts (not on your base; read them with `git show erenup/356-SPEC-t18-draft-a:research/T18/DraftA.lean`,
`git show erenup/356-SPEC-t18-draft-a:research/T18/COMPARISON_A.md`, `git show erenup/357-SPEC-t18-draft-b:research/T18/DraftB.lean`,
`git show erenup/357-SPEC-t18-draft-b:research/T18/COMPARISON_B.md`), the paper `paper/sections/03-torus.tex:287-346`, the registered vocabulary
`verification/Contracts/V1/{TorusData,TorusLocalTheory,Packet,InsertionFamily,Scaling,MaximalPartial}.lean` and `Contracts/V2/InsertionLifespan.lean` (import and use by name;
nothing registered is copied), and the reconciled upstream specs `research/T17/Spec.lean` (its verbatim vocabulary block bundles T13/T14/T15/T16 and defines
`CorrectionAPI`), `research/T15/Spec.lean`, `research/T16/Spec.lean`.

## Ground rules
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. No proofs, no edits to existing modules; new files only.
- **Follow the reconciliation's decisions exactly** (base B; parameters `P : PacketImportAPI ν`, `place : PlacementData P`, `scaling : ScalingAPI P place`, `reference`,
  `correction : CorrectionAPI …`; `ε₀` as a field with `eps_pos`; `MemMixedLebesgueT` and the `s<0` `MemForceSobolevT` guards; `periodicSet` support with the `O(ε)` radius
  and the in-chart clause; `blowup` + `blowup_limsup`; `Ico` cross-transport interval; `energyRate` constant `= correction.energyConst`; registered `alpha`; pressure gauge
  as B; both `force_mem` and `forceDifference_mem`). Where the reconciliation says "check `rfl`", verify with an `example … := rfl` in the spec file and report.

## Anti-stub clause
Every field must be a concrete clause of the theorem in the registered vocabulary: no `True`, no `∃ x, True`, no tautologies, no definitions ignoring their arguments,
no self-made stubs for the imported records (copy the T13/T14/T15/T16/T17 vocabulary **verbatim** from `research/T17/Spec.lean`, delimited with provenance comments,
exactly as draft B did). Before reporting, print `grep -nE ': *True|:= *0$|→ *True' research/T18/Spec.lean` and confirm it is empty. Expect a file comparable to draft B
(~1400 lines) — the union of the vocabulary block and the ~45-field `PeriodicInsertionAPI`.

## Deliverables
1. `research/T18/DraftA.lean`, `DraftB.lean`, `COMPARISON_A.md`, `COMPARISON_B.md`, `REPORT_356.md`, `REPORT_357.md` copied verbatim from the two branches (provenance).
2. `research/T18/Spec.lean`: the reconciled statement — the structure `PeriodicInsertionAPI` (Type-valued) in namespace `BlowupDensity.T18.Spec` with every field's docstring
   citing `03-torus.tex:<line>`, the exact quantifier order and a "non-vacuity" note, plus `def periodicInsertionStatement : Prop` in the paper's quantifier order;
   **elaborates** (`cd verification && lake env lean ../research/T18/Spec.lean`, 0 errors); the `rfl` drift checks against registered spellings.
3. `research/T18/COMPARISON.md`: merged paper-clause → Lean field table with A/B provenance, the R42 counterpart field, and the reconciliation's rulings; §"Proof dependencies"
   copied from the reconciliation §4 (which T11/T12/T13/T15/T16/T17 fields the proof will consume); §"Open questions for the owner" (the three of the reconciliation).
4. Report in four parts (what was stated with field counts / files / deviations from the reconciliation with reasons / commands and results); write it to
   `research/T18/REPORT_360.md` (if a guard blocks the write, put the full report in your final message); commit on your branch.
