# Lane 389-T20-U1-2-6-mean-reduction — T20 wave 1 (codex units): U1 `reductionRegular`, U2 `meanBound` (eq:meanbound), U6 `meanFreeEquation` (eq:meanfree) of `research/T20/T20_SPLIT.md`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/389-T20-U1-2-6-mean-reduction` (git branch `erenup/389-T20-U1-2-6-mean-reduction`, based on `origin/erenup/integration-section3`;
the T20 canonical module `Section3/T20/CriticalRegularity.lean` is in lane 381's worktree `/data_8T/ping/blowup_density/.claude/worktrees/381-T20-canonical` (in review) — run
`git merge --no-edit erenup/381-T20-canonical` in your worktree first (allowed for this lane) so the canonical `CriticalRegularityTAPI` and its field spellings are available).
Read `CLAUDE.md`, **`research/T20/T20_SPLIT.md` §0 and units U1, U2, U6 (targets verbatim, inputs with file:line, routes)**, `research/T20/Spec.lean`, `research/T20/probes/api_on_canonical.lean`,
the T11 mean reduction (`Section3/T11/Assembly.lean` `periodicMeanReductionAPI`: `mean_formula`, `mean_derivative`, `transformed_*`; `Section3/T11/MeanIdentity.lean`, `GalileanClasses.lean`),
T10/T12 (`meanT`, `meanZeroPartT`, `spectralGap`), and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No placeholders, no aliases, no named inputs, no goal repackaging.** A `def X : Prop := <goal>` or a hypothesis equal to the target is a stub and will be discarded without review;
  an honest partial with the exact residual statement and error text is fine.
- Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`.

## Goal
New module `formalization/NSFormalization/Section3/T20/MeanReduction.lean` (namespace `NSFormalization.Section3.T20`) with the three fields **verbatim** as theorems: `reductionRegular`
(the mean/mean-free reduction of regularity — route per the split: T11 `transformed_*` + `mean_formula`), `meanBound` (`eq:meanbound`: the mean is controlled by the force's mean integral —
`paper/sections/03-torus.tex` line cited in the split), `meanFreeEquation` (`eq:meanfree`: the mean-free part solves the transformed equation — T11 `mean_derivative`). Follow the split's
routes; if a route needs a T12 field not yet proved (`velocityCriticalL3` etc.), it is NOT in these three units — say so and stop at the exact residual.

## Deliverables
1. `Section3/T20/MeanReduction.lean`; 2. probe `research/T20/probes/mean_reduction_closes.lean` (the three canonical fields closed by `exact`; non-vacuity on a nonzero constant/mode instance);
3. `research/T20/ATTEMPTS_U1_2_6.md`, `research/T20/axioms_u1_2_6.lean`, status in `research/T20/T20_SPLIT.md`, report `research/T20/REPORT_389.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T20.MeanReduction` (0 errors), `lake env lean` on module / probe / axioms file; `make check`.

## Report
Commit on your branch; end with four parts. Also write it to `research/T20/REPORT_389.md`.
