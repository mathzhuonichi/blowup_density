# Lane 169-A01-b1-ladder-r2 — A01 unit B1, time-regularity ladder rung R2: the datum path is differentiable in time

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working
directory `/data_8T/ping/blowup_density/.claude/worktrees/169-A01-b1-ladder-r2` (git branch
`erenup/169-A01-b1-ladder-r2`, based on `origin/erenup/integration`, which now contains lane 161's
`Section4/A01/DatumPathContinuous.lean` and lane 163's `Section4/C01/Enstrophy.lean`). Read `CLAUDE.md`,
`collaboration/HANDOFF.md` §0 (rules) and §2 P8, `research/A01/B1_LADDER.md` (lane 161's ladder table —
rows R1 done, R2/R3/R4), and the top 40 lines of `logs/LESSONS.md` first.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree. Never touch the root checkout or any other worktree. Never
  `git push`, never merge, never rebase. Committing on your own branch is allowed.
- Lean: `. scripts/lean-env.sh` in every shell; `lake` ONLY from `verification/`
  (`cd verification && LEAN_NUM_THREADS=6 lake build …`); drafts via `lake env lean ../research/A01/<file>.lean`.
- No `sorry`, `admit`, `axiom`, `native_decide`; `set_option maxHeartbeats N in` only per declaration,
  `N ≤ 400000`, commented. No edits to existing modules; new files only.
- Before claiming a lemma is "not in the tree", `grep -rn` all of
  `formalization/NSFormalization/Section4/{D01,A03,A04,A01,C01}` and `Source/`, `Paper1/`, `Paper3/`.
  Before citing a paper line, `sed -n` it.
- Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity
  `example` (`u := 0`, `U := 0`).

## Goal — rung R2
Lane 161 proved (`DatumPathContinuous.exists_continuous_datumPath`): for the cylinder pair `(u, U)` on
`Icc 0 S` from `Section4/A01/Horizon.lean:137` `localTheory_on_prescribed_horizon` (angle invariance
`hu`, descent `hU : ∀ t, ordinaryLift (U t) = value 1 (u t)`, and the Duhamel equation
`hduh : ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl (coefficients 1 hq (sobolevPath F hF q)) (ordinarySobolev (q+1) a.toLp a.translation_contDiff) u t`),
every order `m ≤ q+1` has a **continuous** datum path `A_m : Icc 0 S → RealVectorSobolev m` of the
slices `⇑(U t)`. Rung **R2**: the datum path is **differentiable in time** on the interior, with derivative
the datum of the momentum residual `f − (u·∇)u + νΔu − ∇p` (= `∂ₜu`) — i.e. the `H^m`-valued path is
`C¹` in time with the expected derivative, which is the Duhamel equation differentiated.

Two routes; pick the one that closes, record the other:
- (α) **Vendor Duhamel route**: the cylinder array `u : C(Icc 0 S, SobolevSpace 1 (q+1))` satisfies the
  quadratic Duhamel identity; the vendor has time-derivative results for Duhamel paths (grep
  `vendor/NavierStokesAndEuler` and `formalization/FormalPatched` for `hasDerivAt`, `derivWithin`,
  `duhamel`, `sobolevPath_hasDerivWithinAt`, `EulerSmoothFieldSobolevTime`, `OrdinaryWordTime`) — descend
  the word-level derivative to the ordinary `L²` datum with lane 153's `L2Descent` machinery.
- (β) **Physical-side route**: use the tree's `A04/TimeDerivative.lean` (`timeDeriv_isSobolevDatum`,
  `2 ≤ m`, datum of `∂ₜu` under `HasSmoothSobolevPath`) and `C01/JetPaths.lean` / `PressureJetPath.lean`
  (jet-continuous residual and `∂ₜu` paths for a `ClassicalSolutionR`) — but those need a
  `ClassicalSolutionR`, which is what B1 is building; so (β) is only usable if you can phrase R2 for the
  **smooth representative slices** `Z t` of `⇑(U t)` (lane 157/162 pattern) with the Duhamel equation as
  the input instead of `w.momentum`.

## Deliverables
1. New module `formalization/NSFormalization/Section4/A01/DatumPathDeriv.lean`
   (namespace `NSFormalization.Section4.A01`):
   - `datumPath_hasDerivAt` (or `_hasDerivWithinAt` on `Ioo 0 S`): for `m` in the largest range you can
     close (at least `m = 0`; ideally `m ≤ q − 1`), the continuous datum path `A_m` of lane 161 (or a
     path you construct with the same defining property) satisfies
     `∀ t ∈ Ioo 0 S, HasDerivAt A_m (A'_m t) t` where `A'_m t` is an order-`m` datum of the momentum
     residual at time `t` (state exactly which residual expression: the Leray-projected
     `P(f − (u·∇)u) + νΔu` or the physical `f − (u·∇)u + νΔu − ∇p`; the Duhamel equation gives the
     projected form);
   - the identification of `A'_m t` with the datum of `∂ₜ` of the smooth representative (if reachable),
     so that R3 can iterate.
   If R2 does not close at any order, deliver the reduction: the exact vendor/tree statement missing,
   with the error text, plus whatever partial rungs close (e.g. the derivative of the *word paths*
   `t ↦ word 1 (u t) hn w` from the Duhamel identity).
2. Update `research/A01/B1_LADDER.md` row R2 (DONE with the statement, or the exact residual) and add
   R2's sub-rows if you split it. Records `research/A01/ATTEMPTS_B1_R2.md`; conformance
   `research/A01/axioms_b1_r2.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.DatumPathDeriv` (silent),
`lake env lean` on the module (0 output), the axioms file, `make check` from the worktree root.

## Report
Commit on your branch and end with a four-part report: 1. theorems proved (names, exact statements,
orders covered); 2. what is in Lean now; 3. gaps (exact residual, which route, error text); 4. commands
and results. Also write it to `research/A01/REPORT_169.md`.
