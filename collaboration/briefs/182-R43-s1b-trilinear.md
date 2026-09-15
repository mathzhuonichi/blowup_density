# Lane 182-R43-s1b-trilinear — R43 row S1b: the trilinear estimate |⟪(u·∇)u, Λu⟫| ≤ C₀·y·z²

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working
directory `/data_8T/ping/blowup_density/.claude/worktrees/182-R43-s1b-trilinear` (git branch
`erenup/182-R43-s1b-trilinear`, based on branch `erenup/184-MAINT-merge-main` = `origin/erenup/integration` **plus** the merge of `origin/main`
(lane 184); it contains lane 175's `Section4/R43/CriticalPairing.lean` (the consumer: `CriticalTrilinearEstimate`,
`rcritical1_of_trilinear`), lane 165's `Section4/A05/CriticalL3.lean` (`velocityCriticalL3`, `‖z‖₃ ≤ C·‖z‖_{Ḣ^{1/2}}`,
with the U6 scalar Riesz realization `u6_scalar_eLpNorm_le` valid for all `0 < a < 3/2`), the owner's
`Section4/C01/SobolevTwo.lean`, and B02's homogeneous tools). Read `CLAUDE.md`, `collaboration/HANDOFF.md` §0
and §2 P5, `research/R43/R43_SPLIT.md` row S1b (`:64`), `research/R43/REVIEW_175-R43-s1-pairing.md`,
`research/A05/COMPARISON.md`, and the top 40 lines of `logs/LESSONS.md` first.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`,
  commented. No edits to existing modules; new files only.
- Before claiming a lemma is "not in the tree", `grep -rn` all of `Section4/{A05,B02,D01,A03,C01,R43}`, `Source/`,
  `Paper1/`. Before citing a paper line, `sed -n` it. Every declaration must print exactly
  `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`.

## Goal
`04-whole-space.tex:97-99` (eq:Rcritical1's nonlinear term): `|⟨(u·∇)u, Λu⟩| ≤ C₀ ‖u‖_{Ḣ^{1/2}} ‖u‖²_{Ḣ^{3/2}}`
(`y·z²`). Standard route: Hölder `|⟨(u·∇)u, Λu⟩| ≤ ‖u‖₃ ‖∇u‖₃ ‖Λu‖₃` (three factors in `L³`, `1/3+1/3+1/3 = 1`),
then the critical embeddings `‖u‖₃ ≤ C ‖u‖_{Ḣ^{1/2}}` (lane 165), `‖∇u‖₃ ≤ C ‖∇u‖_{Ḣ^{1/2}} = C ‖u‖_{Ḣ^{3/2}}`
and `‖Λu‖₃ ≤ C ‖Λu‖_{Ḣ^{1/2}} = C ‖u‖_{Ḣ^{3/2}}` (the same embedding applied to `∇u` and `Λu`, whose
`Ḣ^{1/2}` data are the order-shifted data of `u` — the "derivativeCriticalL3" the split names as draft-only:
prove it from `u6_scalar_eLpNorm_le` at the shifted datum, or from `velocityCriticalL3` applied to the derivative
field). Work at the datum level used by `CriticalPairing.lean` (`hcrit.advectionHalf`, `hcrit.velocityHalf`,
`hcrit.velocityThreeHalf`): the target is exactly `CriticalTrilinearEstimate (C₀ := C₀) hcrit` for an explicit
`C₀` (product of the embedding constants), so that `rcritical1_of_trilinear` becomes conditional on `hcrit` alone.

## Deliverables
1. New module `formalization/NSFormalization/Section4/R43/Trilinear.lean` (namespace
   `NSFormalization.Section4.R43`): `derivativeCriticalL3` (embedding for the shifted data), the Hölder step at
   datum/`Lp` level (`Lp` Hölder for three factors: grep Mathlib `MeasureTheory.eLpNorm` Hölder lemmas /
   `ENNReal.lintegral_mul_le_Lp_mul_Lq`), and `criticalTrilinearEstimate_of_hcrit : ∀ hcrit, CriticalTrilinearEstimate (C₀ := trilinearConst) hcrit`
   with `trilinearConst` explicit and positive. If the advection pairing at datum level needs an identity between
   `hcrit.advectionHalf` and the physical `(u·∇)u` slice (check how `CriticalDatumPath` states it), prove that
   identity or isolate it as one named hypothesis with the exact statement.
2. Corollary `rcritical1_of_hcrit` (compose with `rcritical1_of_trilinear`). Records
   `research/R43/ATTEMPTS_S1B.md`; conformance `research/R43/axioms_s1b.lean`; update `R43_SPLIT.md` row S1b.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.R43.Trilinear` (silent), `lake env lean`
on the module (0 output), the axioms file, `make check` from the worktree root.

## Report
Commit on your branch; end with four parts (theorems with exact statements and constants / files / gaps with
error text / commands). Also write it to `research/R43/REPORT_182.md`.
