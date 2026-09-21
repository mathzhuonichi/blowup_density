# Lane 166-R44-split — R44: split Proposition 4.4 and prove its cheap rows (HANDOFF P6)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working
directory `/data_8T/ping/blowup_density/.claude/worktrees/166-R44-split` (git branch
`erenup/166-R44-split`, based on `origin/erenup/integration`). Read `CLAUDE.md`,
`collaboration/HANDOFF.md` §0 (rules) and §2 P6, and the top 40 lines of `logs/LESSONS.md` first.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree. Never touch the root checkout `/data_8T/ping/blowup_density` or any
  other worktree. Never `git push`, never merge, never rebase. Committing on your own branch is allowed.
- Lean: `. scripts/lean-env.sh` in every shell; `lake` ONLY from `verification/`
  (`cd verification && LEAN_NUM_THREADS=6 lake build …`); drafts via `lake env lean ../research/R44/<file>.lean`.
- No `sorry`, `admit`, `axiom`, `native_decide`; no edits to existing modules or contracts; new files only.
- **Audit `verification/contracts.json` scopes before assuming a sibling clause exists**: fields in
  `research/*/Spec.lean` are drafts, not registered contracts (this mistake is LESSONS-recorded).
- Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; include non-vacuity examples.

## Goal
Do for Proposition 4.4 (`04-whole-space.tex:134-172`, `L²` critical regularity) exactly what lane 159
did for Proposition 4.3: read `research/R44/Spec.lean` (`RCritical2API`, 9 fields),
`research/R44/COMPARISON.md` (blind drafts A/B reconciled; gaps G1 J-weight identity, G2 eq:Rcritical2,
G3 `H^{-1/2}` force slices), `research/R44/RECONCILIATION.md`, and the model lane's outputs
`research/R43/R43_SPLIT.md`, `research/R43/REVIEW_SPLIT.md`, `Section4/R43/Pieces.lean`.

## Deliverables
1. `research/R44/R44_SPLIT.md`: the proof route of Prop 4.4 as rows (the `J`-weighted energy
   inequality eq:Rcritical2, the regularized division / bootstrap, the embedding step, the `H²`
   integral finiteness, the lifespan clause, the `a = 0` clause), each with: exact Lean shape,
   which registered contract field or tree lemma supplies it (cite `contracts.json` id + version),
   or the precise gap with owner (A04 V3 / C01 V4 / A05 V2 / D01 G1–G3 / R44-own), size, dependencies.
   Mark explicitly what blocks *stating* vs *proving*.
2. New module `formalization/NSFormalization/Section4/R44/Pieces.lean` (namespace
   `NSFormalization.Section4.R44`) with the cheapest closable rows: spelling pins (`ℕ`-pow vs rpow in
   `ℝ≥0∞`, reuse `R43.Pieces` if identical — do not duplicate, import it), the constant arithmetic
   (radius shrinkings and absorption-gate discharge, in C01's exact gate shape), and the scalar
   bootstrap reused from `Paper1/ScalarEnergy.lean` (`critical_norm_bound` / `continuous_bootstrap`)
   or lane 154's `C01.sqrt_energy_le_primitive'` for the `J`-weighted quantity. Prove whichever close fully.
3. Records: `research/R44/ATTEMPTS_R44.md`; conformance `research/R44/axioms_r44_pieces.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.R44.Pieces` (silent),
`lake env lean` on the module (0 output), the axioms file, `make check` from the worktree root.

## Report
Commit on your branch and end with a four-part report: 1. theorems proved; 2. what is in Lean now;
3. gaps (the split-table summary with sizes and blockers); 4. commands and results.
Also write it to `research/R44/REPORT_166.md`.
