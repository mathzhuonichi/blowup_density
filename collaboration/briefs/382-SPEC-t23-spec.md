# Lane 382-SPEC-t23-spec — produce the reconciled specification of T23 (`cor:boundary`, interior no-slip insertion on a bounded domain) from the lead's reconciliation of the two blind drafts

You are a Lean 4 (v4.34.0-rc2 + Mathlib) **specification** worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/382-SPEC-t23-spec` (git branch `erenup/382-SPEC-t23-spec`, based on `origin/erenup/integration-section3` **after** the commit
"T23 reconciliation (Opus draft, lead-approved)", so `research/T23/RECONCILIATION.md` is on your base — verify with `ls research/T23/`). Read `CLAUDE.md` (contract import rules; no
placeholder `Prop`s; docstrings cite paper lines), then **the lead's decisions `research/T23/RECONCILIATION.md` (binding: §2 rulings, §3 decisions, §"False clauses / traps" — in
particular the cube-free `DomainPlacementData` centred at `x₀` with `interiorBall_in_domain`, the un-periodized whole-space `scaledPacket` on Ω, `ClassicalSolutionOmega`,
`IsBoundedBoxOrSmoothDomain`, the consumed (not threaded) whole-space `ScalingAPI`/`CorrectionAPI`, the threaded unregistered T22 norm layer)**, the two blind drafts (not on your base;
read them with `git show erenup/368-SPEC-t23-draft-a:research/T23/DraftA.lean`, `git show erenup/368-SPEC-t23-draft-a:research/T23/COMPARISON_A.md`,
`git show erenup/374-SPEC-t23-draft-b:research/T23/DraftB.lean`, `git show erenup/374-SPEC-t23-draft-b:research/T23/COMPARISON_B.md`), the paper `paper/sections/03-torus.tex:632-667`,
the registered vocabulary `verification/Contracts/V1/{Data,Packet,PacketImport,Scaling,Correction,MaximalPartial,HomogeneousNorm,InsertionFamily,TorusData,TorusLocalTheory}.lean`
and `Contracts/V2/InsertionLifespan.lean` (import and use by name), the reconciled T18 spec `research/T18/Spec.lean` (field-for-field model where the proof is the same) and
the reconciled T22 spec `research/T22/Spec.lean` (copy verbatim the bounded-domain norm layer you use, delimited with provenance comments).

## Ground rules
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. No proofs, no edits to existing modules; new files only.
- **Follow the reconciliation's decisions exactly.** Never import `formalization/NSFormalization/Paper1/BoundaryCorollary.lean` (it has a `sorry`); cite it only.

## Anti-stub clause
Every field must be a concrete clause of the corollary in the registered/copied vocabulary: no `True`, no `∃ x, True`, no tautologies, no definitions ignoring their arguments,
no self-made stubs for the imported records; no origin-centred or cube-bound placement (the two traps of §"False clauses"). Before reporting, print
`grep -nE ': *True|:= *0$|→ *True' research/T23/Spec.lean` and confirm it is empty.

## Deliverables
1. `research/T23/DraftA.lean`, `DraftB.lean`, `COMPARISON_A.md`, `COMPARISON_B.md` (and `REPORT_368.md`/`REPORT_374.md` where they exist) copied verbatim from the two branches.
2. `research/T23/Spec.lean`: the reconciled statement — `DomainPlacementData`, `ClassicalSolutionOmega`, `IsBoundedBoxOrSmoothDomain`, the T22 norm-layer copy, `structure BoundaryInsertionAPI`
   (Type-valued, per §3's field roster incl. `maximal`) with every field's docstring citing `03-torus.tex:<line>`, the exact quantifier order and a "non-vacuity" note, and
   `def boundaryInsertionStatement : Prop`; **elaborates** (`cd verification && lake env lean ../research/T23/Spec.lean`, 0 errors); `rfl` drift checks where a copied block
   overlaps a registered name.
3. `research/T23/COMPARISON.md`: merged paper-clause → Lean field table with A/B provenance, the T18 counterpart field, and the rulings; §"Proof dependencies" copied from the
   reconciliation §4; §"Open questions for the owner".
4. Report in four parts (what was stated with field counts / files / deviations from the reconciliation with reasons / commands and results); write it to `research/T23/REPORT_382.md`
   (if a guard blocks the write, put the full report in your final message); commit on your branch.
