# Lane 234-R41D-small-gaps — R41D gaps G2–G5: the four small class/norm facts the density branch needs (`F_rd ⊆ F_R`, rapid-class closure under compact corrections, `S_σ ⊆ X_R`, `‖0‖ = 0`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/234-R41D-small-gaps` (git branch `erenup/234-R41D-small-gaps`, based on `origin/erenup/integration`). Read `CLAUDE.md`,
`collaboration/HANDOFF.md` §0, the top 40 lines of `logs/LESSONS.md`, then `research/R41D/COMPARISON.md` §3 (gap table **G2–G5**, `:64-72`, exact Lean shapes) and the table
"Reported gaps that are already closed or are local algebra" right below it (`:74-90`) — **first verify for each of G2–G5 whether a later lane already proved it**: `grep -rn` in
`formalization/NSFormalization/Section4/{D01,R41,R45}`, `verification/Contracts/V1/{Data,DatumLemmas}.lean`, `verification/Bindings/` for `MemForceRapid`, `forceClassRapid`, `MemForceCompact`,
`initialClassSchwartz`, `forceSobolevENorm … 0`, and `research/R45/` if it exists. Then the definitions: `verification/Contracts/V1/Data.lean:509-580` (`initialClassR`, `initialClassSchwartz`,
`MemForceR`, `forceClassR`, `forceClassCompact`, `MemForceRapid`, `forceClassRapid`), `:225-236` (`forceSobolevENorm`), the local restatements in `Section4/D01`/`Section4/A02/Restrict.lean` §0
(where `MemForceR` lives for `formalization/`), and the paper `02-preliminaries.tex:20-60` (the force classes) and `04-whole-space.tex:190-200` (`:195` the typed `S_σ` specialization).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; heartbeats ≤ 400000 per declaration if ever needed. No edits to existing modules; new files only.
  Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; non-vacuity `example`s (a nonzero rapid force if one exists in the tree, `0` otherwise).
- **Satisfiability rule:** if a fact is genuinely false as stated (e.g. a class inclusion that the definitions do not give), do NOT weaken silently: prove the closest true statement and
  write the exact discrepancy with `Data.lean` line numbers into `research/R41D/COMPARISON_SMALL_GAPS.md` for the owner.

## Goal (prove those still open; for the closed ones, cite the existing lemma in the records)
- **G2:** `∀ f, MemForceRapid f → MemForceR f` (equivalently `forceClassRapid ⊆ forceClassR`).
- **G3:** `∀ g f, MemForceRapid g → MemForceCompact (fun z => f z - g z) → MemForceRapid f` (rapid class closed under compactly supported corrections).
- **G4:** `initialClassSchwartz ⊆ initialClassR`.
- **G5:** `∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) → ∀ s : ℝ, forceSobolevENorm q s (0 : SpaceTimeField) = 0` (and, if cheap, for every `q`), plus the pointwise `g - g = 0` remark the table mentions.

## Deliverables
1. New module `formalization/NSFormalization/Section4/R41/ClassFacts.lean` (namespace `NSFormalization.Section4.R41`) with the local-vocabulary statements, and the audit
   `research/R41D/axioms_class_facts.lean` including `Contracts.V1.Data`-vocabulary conformance theorems (`rfl` bridges for the classes) so the binding layer can use them directly.
2. Records `research/R41D/ATTEMPTS_SMALL_GAPS.md`, update `research/R41D/COMPARISON.md` rows G2–G5.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.R41.ClassFacts` (silent), `lake env lean` on the module (0 output), the audit, `make check`.

## Report
Commit on your branch; end with four parts. Also write it to `research/R41D/REPORT_234.md`.
