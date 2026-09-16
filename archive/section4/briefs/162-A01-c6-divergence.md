# Lane 162-A01-c6-divergence — A01 constructor row c6: divergence-free velocity slices

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working
directory `/data_8T/ping/blowup_density/.claude/worktrees/162-A01-c6-divergence` (git branch
`erenup/162-A01-c6-divergence`, based on `origin/erenup/integration`). Read `CLAUDE.md`,
`collaboration/HANDOFF.md` §0 (rules) and §2 P7 (P7a), and the top 40 lines of `logs/LESSONS.md` first.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree. Never touch `/data_8T/ping/blowup_density` (root checkout) or any
  other worktree. Never `git push`, never merge, never rebase. Committing on your own branch is allowed.
- Lean setup: every shell must first run `. scripts/lean-env.sh`; run `lake` ONLY from
  `verification/` (`cd verification && LEAN_NUM_THREADS=6 lake build …`); drafts via
  `cd verification && lake env lean ../research/A01/<file>.lean`.
- No `sorry`, `admit`, `axiom`, `native_decide`. `set_option maxHeartbeats N in` only per
  declaration with `N ≤ 400000` and a comment. Do not edit existing modules; new files only.
- Before claiming a lemma is "not in the tree", `grep -rn` all of
  `formalization/NSFormalization/Section4/{D01,A03,A04,A01,C01}`. Before citing a paper line, `sed -n` it.
- Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; include a
  non-vacuity `example`.

## Goal
Row **c6** of the mild ⇒ classical constructor (`research/A01/A01_SPLIT.md:107`): the constructed
velocity is divergence free, `∀ t ∈ Ico 0 T, ∀ x, spatialDivergence velocity t x = 0`
(`Section4/A02/SolutionClass.lean`, field `divergence`). Do the **a.e. part** from the cylinder
data now; the pointwise upgrade belongs to c3 (joint smoothness, another lane).

Inputs: the cylinder pair `(u, U)` output by `Section4/A01/Horizon.lean:137`
`localTheory_on_prescribed_horizon`, in particular its clause
`∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0` and the descent `∀ t, ordinaryLift (U t) = value 1 (u t)`,
plus a candidate `velocity : SpaceTimeField` with `hslice : ∀ t, (fun x => velocity (↑t, x)) =ᵐ[volume] ⇑(U t)`.

Context: `research/A01/C1B_SPLIT.md` (carrier bridge rows, esp. c6), `Section4/A01/EulerPairing.lean`
(descent of derivative words: `exists_descend`, `weakDeriv_pairing_of_lift_hasDerivAt`),
`Section4/A01/L2Descent.lean` (`word_descent_ae_top`: descent at all orders with no jet loss),
`Section4/A01/CarrierWords.lean` (`word_descent_ae_partial`: descended word = classical jet a.e. of a
smooth representative), `Section4/D01/OrderZeroCurl.lean` / `LerayLowering.lean` / `LerayDatum.lean`
(the tree's notion of divergence-free data at datum level), and the HeliCorgi source cited by the
split: `vendor/HeliCorgi/Formal/R3InversionConsistency.lean:139`
(`r3DecodedFrequency_incompressible_ae_decoder`). Find the vendor definition of
`divergenceFreeSpace` and what it says about the coordinate derivative words (`∑ᵢ ∂ᵢ uᵢ = 0` at the
lift/word level).

## Deliverables
1. New module `formalization/NSFormalization/Section4/A01/ConstructorDivergence.lean`
   (namespace `NSFormalization.Section4.A01`):
   - `divergence_ae_of_cylinder`: from `(u, U)`, `hu`, `hU`, the divergence-free clause, and a
     smooth representative `Z : SmoothL2Field Space` of `⇑(U t)` (as in `L2Descent`/`SliceWiring`,
     `Z.field =ᵐ ⇑(U t)`), conclude `∑ᵢ fderiv ℝ Z.field x (coordinateVector i) i = 0` for a.e. `x`
     (state it in the tree's spelling: `spatialDivergence`-style sum, or the `A02` divergence of the
     slice); derive it by descending the three derivative words `∂ᵢ uᵢ` and summing.
   - `divergence_of_cylinder_pointwise_of_contDiff`: if moreover the candidate `velocity` slice is
     `ContDiff ℝ ∞` (the c3 hypothesis, taken as a named hypothesis here), upgrade a.e. to
     pointwise (continuity + a.e.-zero ⇒ zero) so the `ClassicalSolutionR.divergence` field shape is
     produced verbatim.
2. Records: `research/A01/ATTEMPTS_C6.md`; conformance `research/A01/axioms_c6.lean`
   (`#print axioms` for every declaration, non-vacuity on `u := 0`, `U := 0`).
3. Update `research/A01/CONSTRUCTOR_SPLIT.md` row c6 if that file exists in this worktree; otherwise
   append a lane-162 note to `research/A01/A3_SPLIT.md`.

## Gates (run all, paste outputs)
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.ConstructorDivergence`
(silent), `lake env lean` on the module (0 output), `lake env lean ../research/A01/axioms_c6.lean`,
`make check` from the worktree root.

## Report
Commit on your branch and end with a four-part report: 1. theorems proved (names, exact statements);
2. what is in Lean now; 3. gaps (exact residual with error text if something did not close);
4. commands and results. Also write it to `research/A01/REPORT_162.md`.
