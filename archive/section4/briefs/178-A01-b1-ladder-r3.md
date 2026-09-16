# Lane 178-A01-b1-ladder-r3 — A01 unit B1, ladder rung R3: iterated time regularity `C^j_t H^m_x` of the datum paths

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working
directory `/data_8T/ping/blowup_density/.claude/worktrees/178-A01-b1-ladder-r3` (git branch
`erenup/178-A01-b1-ladder-r3`, based on `origin/erenup/integration`, which contains lane 161's
`Section4/A01/DatumPathContinuous.lean` (R1) and lane 169's `Section4/A01/DatumPathDeriv.lean` (R2:
`exists_differentiable_datumPath`, `projectedResidualPath_eq`, `residualDatum_is_timeDerivative`)). Read
`CLAUDE.md`, `collaboration/HANDOFF.md` §0 and §2 P8, `research/A01/B1_LADDER.md` (rows R1/R2 DONE, R3 at `:16`,
§"R3/R4" at `:98-110`), `research/A01/REPORT_169.md`, `research/A01/REVIEW_169-A01-b1-ladder-r2.md`, and the top
40 lines of `logs/LESSONS.md` first.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`,
  commented. No edits to existing modules; new files only.
- Before claiming a lemma is "not in the tree", `grep -rn` all of `Section4/{D01,A03,A04,A01,C01}`, `Source/`,
  `Paper1/`, `Paper3/`, the vendor and `FormalPatched/`. Before citing a paper line, `sed -n` it.
- Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`
  (`u := 0`, `U := 0`).

## Goal — rung R3 (`B1_LADDER.md:16`)
`∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m:ℝ), ContDiffOn ℝ j G (Icc 0 S) ∧ ∀ t, IsSobolevDatum m (⇑(U t)) (G t.1)`
— the datum path of the velocity slices is `C^j` in time at every order `m`, for the cylinder pair `(u, U)`
of `localTheory_on_prescribed_horizon` (`Section4/A01/Horizon.lean:137`). R2 gives `C¹` with derivative the
order-`m` datum of the projected residual `νΔu + P(F − (u·∇)u)`. R3 is the bootstrap
(`paper/sections/appendix-a-local-theory.tex:71-76`): differentiate the residual again — `Δu`'s datum path is
the order-`(m+2)` velocity path lowered by two orders (so its time derivative is R2 at order `m+2`), the force
path `F` is smooth in time (lane 167's `forcePath_of_memForceR` / `MemForceR`'s `ContDiffOn ℝ ∞ G futureTimes`),
and the bilinear term `P((u·∇)u)` needs the product rule for the datum-level tame product
(`Section4/A03/VectorTameProduct.lean`, `Section4/D01/…` — find the Leibniz/product-of-paths lemma; lane 145/155's
`FiniteOrderNorm` for norm control). Induct on `j`, losing orders each time (`m ≤ q − 1 − 2j` or whatever the
bookkeeping forces); state the exact range. Since orders are lost at each step, the "all orders on one horizon"
statement needs the supply-side all-order bound (`B1_LADDER.md` §R3/R4, A3): if that is genuinely needed, isolate
it as a named hypothesis `hall : ∀ m, HasAprioriBoundInv …` (lane 173's predicate, on `origin/erenup/integration`
as `Section4/A01/AprioriInvariance.lean` once merged — check; else state the bound shape from `Horizon.lean:106`)
and prove R3 conditional on it, with the unconditional version for the finite range that closes.

## Deliverables
1. New module `formalization/NSFormalization/Section4/A01/DatumPathSmooth.lean` (namespace
   `NSFormalization.Section4.A01`): `residualPath_hasDerivAt` (the projected residual datum path is itself
   differentiable, derivative computed), `datumPath_contDiffOn` (R3 for the closable range, exact statement),
   and the conditional all-order version if needed.
2. Update `research/A01/B1_LADDER.md` row R3 (DONE range / residual) and R4's inputs; records
   `research/A01/ATTEMPTS_B1_R3.md`; conformance `research/A01/axioms_b1_r3.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.DatumPathSmooth` (silent),
`lake env lean` on the module (0 output), the axioms file, `make check` from the worktree root.

## Report
Commit on your branch; end with four parts (theorems with exact statements and ranges / files / gaps with error
text / commands). Also write it to `research/A01/REPORT_178.md`.
