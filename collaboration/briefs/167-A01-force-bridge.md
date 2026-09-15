# Lane 167-A01-force-bridge — A01 constructor row (v): datum/forcing bridge `(a, F) ↦ (a', f')` (HANDOFF P7b)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working
directory `/data_8T/ping/blowup_density/.claude/worktrees/167-A01-force-bridge` (git branch
`erenup/167-A01-force-bridge`, based on `origin/erenup/integration`). Read `CLAUDE.md`,
`collaboration/HANDOFF.md` §0 (rules) and §2 P7 (P7b), and the top 40 lines of `logs/LESSONS.md` first.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree. Never touch the root checkout or any other worktree. Never
  `git push`, never merge, never rebase. Committing on your own branch is allowed.
- Lean: `. scripts/lean-env.sh` in every shell; `lake` ONLY from `verification/`
  (`cd verification && LEAN_NUM_THREADS=6 lake build …`); drafts via `lake env lean ../research/A01/<file>.lean`.
- No `sorry`, `admit`, `axiom`, `native_decide`; `set_option maxHeartbeats N in` only per declaration,
  `N ≤ 400000`, commented. No edits to existing modules; new files only.
- Before claiming a lemma is "not in the tree", `grep -rn` all of
  `formalization/NSFormalization/Section4/{D01,A03,A04,A01,C01}`. Before citing a paper line, `sed -n` it.
- Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`.

## Goal
The a-priori-bound machinery of A01 speaks the cylinder-carrier language:
`HasAprioriBound hq hν a F hF R` (`Section4/A01/Horizon.lean:106`) quantifies over
`a : SmoothL2Field Space` and a force path `F : Icc 0 S → SmoothL2Field Space` with
`hF : ∀ n, Continuous fun t => (F t).jetLp n`. The classical solution class speaks the physical
language: `a' : SpatialField` with `a' ∈ initialClassR` (`Section4/A02/SolutionClass.lean:97`),
`f' : SpaceTimeField` with `MemForceR f'` (`Section4/D01/ForceClass.lean:158`: `ContDiffOn ℝ ∞ f' futureDomain ∧ ∀ m, ∃ G, IsSobolevPath m f' G ∧ ContDiffOn ℝ ∞ G futureTimes ∧ MemLp G 1 … ∧ MemLp G 2 …`),
`MemL1Hm f'` (`Section4/A04/Forcing.lean:110`). Row (v) of `research/A01/REVIEW_APRIORI_ROWS.md`
(§"Residual-row audit", table row **(v)**) and `research/A01/REVIEW_L2_DESCENT.md` §3 row 5:
**nothing in `Section4/A01` connects `F` to `f'`**. Lane 146's `C01/JetPaths.lean` `forcePath`
goes the other way (`f ↦ F`), and is the template.

## Deliverables
1. New module `formalization/NSFormalization/Section4/A01/ForceBridge.lean`
   (namespace `NSFormalization.Section4.A01`):
   - `forceOfPath (F : Icc 0 S → SmoothL2Field Space) : SpaceTimeField` — the physical force
     `f' (t, x) := (F (projIcc 0 S _ t)).field x` (or `0` outside `[0,S]`; pick the convention that
     makes `MemForceR` provable and say why; the paper's `F_R` is `C^∞([0,∞); H^∞)` with
     `L¹_t H^m ∩ L²_t H^m` bounds, `02-preliminaries.tex:17-22`);
   - `memForceR_forceOfPath`: `MemForceR (forceOfPath F)` from `hF` (jet continuity gives the
     datum path per order via the datum-from-jets constructor `D01/FiniteOrderConstructor.lean` and
     `D01/DatumToJets.lean`; time smoothness of `G` needs `ContDiffOn` in `t` — if `hF` (continuity
     only) is insufficient for `ContDiffOn ℝ ∞ G futureTimes`, isolate the extra hypothesis
     (`∀ n, ContDiff ℝ ∞ fun t => (F t).jetLp n` or a `SmoothL2Field`-path smoothness) as a named
     hypothesis and record exactly what `localTheory_on_prescribed_horizon`'s `F` actually has);
   - `memL1Hm_forceOfPath` and the round trip `forcePath (forceOfPath F) = F` (or a.e./`rfl` as far
     as it holds) so the two languages agree;
   - `initialClassR_of_smoothL2` : `a.field ∈ initialClassR` for `a : SmoothL2Field Space` with the
     solenoidal condition (find the tree's `divergenceFreeSpace`/`IsSolenoidal` bridge — `Section4/A02/SolutionClass.lean`, `D01/OrderZeroCurl.lean`).
2. Records: `research/A01/ATTEMPTS_FORCE_BRIDGE.md`; conformance `research/A01/axioms_force_bridge.lean`
   (non-vacuity on `F := fun _ => zeroField`, `a := zeroField`); append a lane-167 note to
   `research/A01/A3_SPLIT.md` row (v).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.ForceBridge` (silent),
`lake env lean` on the module (0 output), the axioms file, `make check` from the worktree root.

## Report
Commit on your branch and end with a four-part report: 1. theorems proved (names, exact statements);
2. what is in Lean now; 3. gaps (named hypotheses left, with exact statements); 4. commands and results.
Also write it to `research/A01/REPORT_167.md`.
