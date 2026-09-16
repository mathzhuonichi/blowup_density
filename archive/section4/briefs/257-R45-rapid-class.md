# Lane 257-R45-rapid-class — Corollary 4.5 for the rapidly decaying class `Y = F_rd` and the Schwartz specialization: the `density`, `zeroIff`, `regularReference` fields at `Y = forceClassRapid` and `schwartzDensity` of `research/R45/Spec.lean`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/257-R45-rapid-class` (git branch `erenup/257-R45-rapid-class`, based on lane 234's branch `erenup/234-R41D-small-gaps` = `origin/erenup/integration`
+ `formalization/NSFormalization/Section4/R41/ClassFacts.lean` (G2 `memForceR_of_memForceRapid`/`forceClassRapid_subset_forceClassR`, G3 `memForceRapid_of_compact_difference`, G4
`initialClassSchwartz_subset_initialClassR`, G5 `forceSobolevENorm_zero`; with contract-vocabulary bridges in `research/R41D/axioms_class_facts.lean` — reuse those bridges)). On integration:
lane 252's `verification/Bindings/CompactClassDensity.lean` (`density_compact`, `zeroIff_compact` — **the templates**: replace `forceClassCompact` by `forceClassRapid`, compact closure by G3,
`F_c ⊆ F_R` by G2) and lane 254's rider (branch `erenup/254-R45-compact-rider`, not on your base — read `git show erenup/254-R45-compact-rider:verification/Bindings/CompactClassRider.lean`
for `regularReference_compact`'s proof and copy its route with the rapid closure G3). Read `research/R45/Spec.lean` (the four fields; specialize `Y := forceClassRapid`; `schwartzDensity` is
stated with `a ∈ initialClassSchwartz` — derive it from `density` at `Y = F_rd` via G4), `research/R45/COMPARISON.md`, `research/R45/RECONCILIATION.md`, lane 233's `Bindings/InsertionFromData.lean`
(import caveat: not with `Bindings.Packet`), `CLAUDE.md`, `collaboration/HANDOFF.md` §0, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; heartbeats ≤ 400000 per declaration, commented. No edits to existing modules/Bindings/Tests (234's module is on your base but unmerged — do not edit it);
  new files only. Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; non-vacuity `example`s (`ν = T = 1`, `a = 0`, `g = 0`).
- **Statement fidelity:** the theorems = the Spec fields at `Y = forceClassRapid` (identical binders) and `schwartzDensity` verbatim. **Satisfiability rule:** isolate ONE named hypothesis if a step resists.

## Goal (in `verification/Bindings/RapidClassDensity.lean`, namespace `BlowupDensity.Bindings`)
`density_rapid`, `zeroIff_rapid`, `regularReference_rapid`, `schwartzDensity`; and, if cheap, the combined parametric fields `density`, `zeroIff`, `regularReference` for
`Y = forceClassCompact ∨ Y = forceClassRapid` by `Or.elim` with lane 252/254's compact instances (only if 254's file is on your base — it is not; state the `Or.elim` combination for
`density`/`zeroIff` using 252's landed theorems and leave `regularReference`'s combination to the registration lane). Audit `research/R45/axioms_rapid_class.lean`; records
`research/R45/ATTEMPTS_RAPID.md`; update `research/R45/COMPARISON.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build Bindings.RapidClassDensity` (silent), `lake env lean Bindings/RapidClassDensity.lean` (0 output), the audit, `make check`, `make test`.

## Report
Commit on your branch; end with four parts. Also write it to `research/R45/REPORT_257.md`.
