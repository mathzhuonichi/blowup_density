# Lane 176-MAINT-simp-codex-batch — simplifier/tester pass over the first codex batch (HANDOFF P10)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) maintenance worker on the repository checked out at your working
directory `/data_8T/ping/blowup_density/.claude/worktrees/176-MAINT-simp-codex-batch` (git branch
`erenup/176-MAINT-simp-codex-batch`, based on `origin/erenup/integration`). Read `CLAUDE.md` (hard rule 4:
every merged proof module gets a simplifier + tester pass), `collaboration/HANDOFF.md` §0 and §2 P10,
`research/MAINT/ATTEMPTS_SIMP_155.md` + `research/MAINT/REVIEW_SIMP_155.md` (the previous SIMP pass and how it
was audited), and the top 40 lines of `logs/LESSONS.md` first.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree. Never touch the root checkout or any other worktree. Never
  `git push`, never merge, never rebase. Committing on your own branch is allowed.
- This lane MAY edit existing `formalization/` modules, but: **no theorem consumed by another module or by a
  registered contract's Bindings may change its statement or get weaker** (byte-identical signatures for
  consumed declarations; adding sharper new lemmas is fine); every downstream module must still compile.
- No `sorry`, `admit`, `axiom`, `native_decide`; no new `set_option`; no edits under `paper/`,
  `Contracts/V1`, `Contracts/V2`, `Contracts/V3`, existing `Tests/*`.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.

## Scope — the modules merged from the codex batch and the notes their reviews left
1. `Section4/A01/DatumPathContinuous.lean` (161), `A01/ConstructorDivergence.lean` (162),
   `A01/ConstructorPressure.lean` (168), `C01/Enstrophy.lean` (163), `C01/EnstrophyIdentity.lean` (170),
   `R44/Pieces.lean` (166), `D01/HomogeneousNorm.lean` (164): for each, a simplifier pass — remove dead
   hypotheses (the reviews flagged e.g. an unused binder pattern), replace long `simp`/`rw` chains that a
   tree lemma already proves, hoist duplicated local lemmas into the module that owns them, dedupe against
   `Source/`/`Paper1/` (grep before adding); record line counts before/after.
2. Earlier review leftovers (check each still applies at HEAD): `research/C01/Spec.lean` two `(:103)` → `(:104)`
   citations (review 156); `Section4/C01/EnergyBounds.lean` `sqrt_energy_le_primitive'` ~45-line overlap with
   `Paper1/ScalarEnergy.lean` (hoist the generalized version to `Paper1` and make the old one its corollary,
   keeping the old statement byte-identical); `Section4/A01/SliceWiring.lean` `velocitySliceSmoothL2` alias
   duplicating `C01.velocityField_field` (retire the alias if its only use site can take `velocityField`
   directly; keep `_field` lemma consumers compiling) and `sobolevENorm_slice_ne_top` generalized to any
   order (add the general lemma, keep the old as a corollary).
3. **Tester pass**: for every touched module rerun its conformance file `research/*/axioms_*.lean`
   (must still print exactly `[propext, Classical.choice, Quot.sound]`) and one existing negative probe.
4. **Contract closure**: list which of the A01/C01/R44 modules above are in no registered contract closure
   (`make test` does not compile them); write the exact A01 V2 / C01 V4 bundle plan (which theorems would
   be registered, with explicit named hypotheses) into `research/MAINT/CLOSURE_PLAN.md` — do NOT register
   anything in this lane.

## Gates
`lake build` of every touched module and of the full dependent set (`grep -rln "import NSFormalization.Section4.<Node>.<Module>"
formalization verification research`), then from the worktree root `scripts/gates.sh <touched Section4 modules>`
(runs `make check`, `make test`, `make test-mutations`) and `python3 experiments/check_contracts.py --base-ref origin/erenup/integration`
(exit 0). Paste outputs. Record `research/MAINT/ATTEMPTS_SIMP_176.md` with a table item → files → lines
removed/added → consumers rebuilt; skipped items with reasons.

## Report
Commit on your branch and end with a four-part report: 1. what was simplified (per item); 2. what is in Lean
now (invariance table: consumed statements unchanged); 3. what was skipped and why; 4. commands and results.
Also write it to `research/MAINT/REPORT_176.md`.
