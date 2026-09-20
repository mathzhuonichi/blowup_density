# Lane 161-A01-b1-time-ladder — A01 unit B1, time-regularity ladder, rung 1

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working
directory `/data_8T/ping/blowup_density/.claude/worktrees/161-A01-b1-time-ladder` (git branch
`erenup/161-A01-b1-time-ladder`, based on `origin/erenup/integration`). Read `CLAUDE.md`,
`collaboration/HANDOFF.md` §0 (rules) and §2 P8, and the top 40 lines of `logs/LESSONS.md` first.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree. Never touch `/data_8T/ping/blowup_density` (the root checkout) or
  any other worktree. Never `git push`, never merge, never rebase. Committing on your own branch is
  allowed (`git add` + `git commit` in this worktree only).
- Lean setup: every shell must first run `. scripts/lean-env.sh`; run `lake` ONLY from the
  `verification/` subdirectory (`cd verification && LEAN_NUM_THREADS=6 lake build …`). Draft files
  are checked with `cd verification && lake env lean ../research/A01/<file>.lean`.
- No `sorry`, `admit`, `axiom`, `native_decide`. `set_option maxHeartbeats N in` only per
  declaration with `N ≤ 400000` and a comment. Do not edit existing modules; add new files only
  (plus your `research/A01/` records).
- Before claiming a lemma is "not in the tree", `grep -rn` all of
  `formalization/NSFormalization/Section4/{D01,A03,A04,A01,C01}` — this mistake was made three times
  (see LESSONS). Before citing a paper line, `sed -n` it.
- Every declaration must print exactly `[propext, Classical.choice, Quot.sound]` under
  `#print axioms`; include a non-vacuity `example`.

## Goal
Unit **B1** (`velocity_smooth : ContDiffOn ℝ ∞ velocity (Ico 0 T ×ˢ univ)`) is the single biggest
blocker of the A01 chain. Its time regularity must come from the Duhamel equation. This lane proves
the **first rung of the time-regularity ladder** and writes the ladder as a table.

Context to read (in this order):
1. `research/A01/REVIEW_SLICE_WIRING.md` §3(b) — the target `CarrierConstructorFull` (verified to
   close the consumer loop in `research/A01/probes/rev157_constructor_loop.lean`).
2. `research/A01/A01_SPLIT.md` rows c1–c9 (`:102-110`) and the B1 paragraph (`:207-214`);
   `research/A01/A3_SPLIT.md` lane notes 147–157.
3. `Section4/A01/Horizon.lean:137` (`localTheory_on_prescribed_horizon` — the cylinder pair `(u, U)`
   on `Icc 0 S` with the Duhamel equation `u t = quadraticDuhamel …`, angle invariance, descent
   `ordinaryLift (U t) = value 1 (u t)`).
4. `Section4/A01/L2Descent.lean` (`word_descent_ae_top`, `hword_jet_full`),
   `Section4/A01/CarrierWords.lean`, `Section4/A01/SliceWiring.lean`,
   `Section4/A01/EulerPairing.lean` (`exists_descend`, `hasWeakDerivsL2_of_cylinder`),
   `Section4/D01/FiniteOrderConstructor.lean` (datum from weak derivatives),
   `Section4/D01/DatumToJets.lean` (datum ⇒ smooth jets), `Section4/A04/TimeDerivative.lean`
   (datum of `∂ₜu` from the momentum equation, `2 ≤ m`), `Section4/C01/JetPaths.lean` and
   `PressureJetPath.lean` (jet-continuous residual paths), `Section4/C01/Evolution.lean:115,147`.
5. `paper/sections/appendix-a-local-theory.tex:71-76` (the bootstrap: `W^{1,∞}_t H^k_x` then
   repeated time differentiation gives `C^j_t H^k_x`).

## Deliverables
1. `research/A01/B1_LADDER.md`: the ladder from the cylinder pair to joint `C^∞`, as rows with
   exact Lean statements, the tree lemmas available, gaps, sizes:
   (R1) for each order `m`, a **continuous selection** `t ↦ A_m(t)` of order-`m` data of the velocity
   slices `⇑(U t)` on `Icc 0 S` (not just `∀ t ∃ A`; the choice must be continuous — use the word
   paths `t ↦ word 1 (u t) hn w`, which are continuous because `u` is a `ContinuousMap`, and the
   quantitative constructor of `D01/FiniteOrderNorm.lean` for the norm control);
   (R2) the Duhamel equation gives the time derivative of the order-`m` datum path as the datum of
   the momentum residual (mirror `A04/TimeDerivative.lean` and `C01/JetPaths.residualPath`);
   (R3) induction: `C^j_t H^m_x` for all `j, m`; (R4) Sobolev embedding to pointwise joint `C^∞`.
2. **Prove R1 in Lean**: new module
   `formalization/NSFormalization/Section4/A01/DatumPathContinuous.lean`
   (namespace `NSFormalization.Section4.A01`): for the cylinder pair with `hu`, `hU`, and every
   `m ≤ q + 1` (or the largest range you can close, at least `m ≤ q − 2`), a function
   `A : Icc 0 S → RealVectorSobolev m` with `∀ t, IsSobolevDatum m (⇑(U t)) (A t)` (or the smooth
   representative's slice) and `Continuous A`. If full continuity does not close, prove continuity
   of the `L²` norms `t ↦ ‖A t‖` and state the exact residual.
3. Records: `research/A01/ATTEMPTS_B1_LADDER.md` (every failed route with the exact error text);
   conformance `research/A01/axioms_b1_ladder.lean` (`#print axioms` for every declaration, plus a
   non-vacuity example on `u := 0`, `U := 0`).

## Gates (run all, paste outputs in your report)
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.DatumPathContinuous`
(must be silent for this module), `lake env lean ../formalization/NSFormalization/Section4/A01/DatumPathContinuous.lean`
(0 output), `lake env lean ../research/A01/axioms_b1_ladder.lean`, and `make check` from the worktree root.

## Report
When done, commit on your branch and end with a four-part report (this is what the lead reads):
1. which theorems are proved (names, exact statements); 2. what is in Lean now (files);
3. gaps (the ladder table summary with sizes); 4. commands run and their results.
Also write the same report to `research/A01/REPORT_161.md`.
