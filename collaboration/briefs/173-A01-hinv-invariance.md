# Lane 173-A01-hinv-invariance — A01 residual row (iv): angle invariance of the a-priori-bound solution (HANDOFF P9a)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working
directory `/data_8T/ping/blowup_density/.claude/worktrees/173-A01-hinv-invariance` (git branch
`erenup/173-A01-hinv-invariance`, based on `origin/erenup/integration`). Read `CLAUDE.md`,
`collaboration/HANDOFF.md` §0 (rules) and §2 P9 (P9a), and the top 40 lines of `logs/LESSONS.md` first.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree. Never touch the root checkout or any other worktree. Never
  `git push`, never merge, never rebase. Committing on your own branch is allowed.
- Lean: `. scripts/lean-env.sh` in every shell; `lake` ONLY from `verification/`
  (`cd verification && LEAN_NUM_THREADS=6 lake build …`); drafts via `lake env lean ../research/A01/<file>.lean`.
- No `sorry`, `admit`, `axiom`, `native_decide`; `set_option maxHeartbeats N in` only per declaration,
  `N ≤ 400000`, commented. No edits to existing modules; new files only.
- Before claiming a lemma is "not in the tree", `grep -rn` all of
  `formalization/NSFormalization/Section4/{D01,A03,A04,A01,C01}`, `Source/`, `FormalPatched/`, and the
  vendor. Before citing a paper line, `sed -n` it.
- Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`.

## The problem
`HasAprioriBound hq hν a F hF R` (`Section4/A01/Horizon.lean:106`) quantifies over **every** mild
(quadratic Duhamel) solution `u : C(Icc 0 T, SobolevSpace 1 (q+1))` on every subwindow `T ≤ S` and asks
`‖u‖ ≤ R`. The consumers that *produce* the bound (A3: lane 147 `OrderTwoCap.kbnd_of_sup_bound`, lane 149
`AprioriRows`, lane 157 `SliceWiring.apriori_rows_of_hslice`, lanes 151/153 `hword_jet_full`) all need the
solution to be **angle invariant**: `hu : ∀ θ : AddCircle (1:ℝ), ∀ t, sobolevTranslation 1 (q+1) (0, θ) (u t) = u t`
(the cylinder-carrier encoding of an `ℝ³` field). The `u` that `HasAprioriBound` quantifies over carries only
the Duhamel constraint, not invariance (`research/A01/REVIEW_APRIORI_ROWS.md`, §"Residual-row audit",
"Missing from the list"; `research/A01/REVIEW_SLICE_WIRING.md` N2; `research/A01/A3_SPLIT.md` rows (iv)).
Row **(iv)**: close this gap.

Two routes — do whichever closes, record both:
- (α) **Invariance propagates**: if the datum `a` and the force path `F` are angle invariant (they are —
  `ordinarySobolev (q+1) a.toLp a.translation_contDiff` and `sobolevPath F hF q` come from `ℝ³` objects),
  then every Duhamel solution is angle invariant: `sobolevTranslation (0,θ) (u t)` is again a Duhamel
  solution with the same data (translation commutes with the heat semigroup and the nonlinearity — find the
  vendor/tree lemmas: `Section4/A01/ContinuationInvariant.lean`, `Continuation.lean:147`
  `forced_ordinary_descent`, `Section4/A01/Propagation.lean`, the vendor's `sobolevTranslation` API and
  `quadraticDuhamel` translation-equivariance), and mild solutions on `SobolevSpace 1 (q+1)` are unique
  (vendor uniqueness `Formal…`/`FormalPatched/R3MildContinuation.lean`, or the `OpenAI` package's
  `quadraticDuhamel` uniqueness) — hence `u = translate u`. This gives `hinv` for free for every `u` in
  `HasAprioriBound`'s scope.
- (β) **Restrict the quantifier**: define `HasAprioriBoundInv` quantifying only over angle-invariant
  Duhamel solutions, prove `HasAprioriBound → HasAprioriBoundInv` (trivial) and show that the consumer
  `localTheory_on_prescribed_horizon` / `forced_global_of_bound_unconditional` (`Horizon.lean:137`,
  `Continuation.lean`) still closes with the weaker predicate (its own solution is invariant by
  `forced_ordinary_descent`), so the A3 supply side only owes the weaker bound. Route (β) is the fallback if
  (α)'s equivariance/uniqueness is not in the tree; it is acceptable if the consumer loop is re-closed in Lean.

## Deliverables
1. New module `formalization/NSFormalization/Section4/A01/AprioriInvariance.lean`
   (namespace `NSFormalization.Section4.A01`): for (α) `duhamel_angle_invariant` (exact statement: for the
   data `a`, `F`, `hF`, every `u` with `∀ t, u t = quadraticDuhamel …` satisfies `hu`) and the corollary
   that `HasAprioriBound`'s `u` is invariant; for (β) the predicate, the implication, and the re-closed
   consumer theorem. State clearly which route closed.
2. Records `research/A01/ATTEMPTS_HINV.md` (both routes, the exact vendor lemmas used or missing with error
   text); conformance `research/A01/axioms_hinv.lean`; append a lane-173 note to `research/A01/A3_SPLIT.md` row (iv).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.AprioriInvariance` (silent),
`lake env lean` on the module (0 output), the axioms file, `make check` from the worktree root.

## Report
Commit on your branch and end with a four-part report: 1. theorems proved (names, exact statements, route);
2. what is in Lean now; 3. gaps (exact residual with error text); 4. commands and results.
Also write it to `research/A01/REPORT_173.md`.
