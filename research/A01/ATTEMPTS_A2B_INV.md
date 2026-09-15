# ATTEMPTS — lane 134-A01-a2b-invariance (unit A2b / A3 row A2b-b)

Row **A2b-b**: the angle-invariance clause of the continued forced mild solution, which lane
126 left as the hypothesis `hinv` of `Continuation.forced_global_of_bound'`.  Deliverable
module: `formalization/NSFormalization/Section4/A01/ContinuationInvariant.lean`
(namespace `NSFormalization.Section4.A01`, imports the frozen `…A01.Continuation`, edits
nothing).  Followed the lane-126 reviewer recipe `research/A01/REVIEW_A2B.md` §3.

## Outcome — all four steps closed

Five new theorems, `lake build … ContinuationInvariant` = `Build completed successfully
(3942 jobs)`, `lake env lean` on the module silent (0 bytes), every `#print axioms`
= `[propext, Classical.choice, Quot.sound]`.

1. `restart_window_invariance` — step 1a, the reviewer's Probe 2
   (`research/A01/probes/probe_restart_window_invariance.lean`) promoted verbatim and credited.
   Single-declaration `set_option maxHeartbeats 600000 in` (see §heartbeats).
2. `exists_uniform_restart_time_invariant` — step 1b.
3. `gluePath_invariant` — step 2.
4. `forced_global_mild_of_bound_invariant` — step 3, the forked induction.
5. `forced_global_of_bound_unconditional` — step 4, `forced_global_of_bound'` with `hinv`
   discharged by step 3.

## Design decisions (what worked, and the one place I diverged from the recipe)

* **Step 1b via `min`, not by re-deriving `δ` (divergence from the recipe, lower risk).**
  The reviewer's §3 step 1 suggested *merging* the ~20-line existence body of
  `exists_uniform_restart_time` with Probe 2's invariance body into one `δ` obtained from
  `exists_positive_time_budget`.  I instead used **both** as black boxes: obtain the vendor
  existence `δ₁` from `EulerUniformHeatLocal.exists_uniform_restart_time` and the invariance
  `δ₂` from `restart_window_invariance (R := R+1)`, and return `min δ₁ δ₂`.  On windows
  `T ≤ min δ₁ δ₂` both clauses fire (`le_trans hTδ (min_le_left/right _ _)`).  This reuses two
  already-checked proofs unchanged and needs no `set_option` on the combined theorem.
  Consistency of the contraction regime is automatic: the vendor `δ₁` is derived from
  `exists_positive_time_budget ν (C.ballBound (R+1)) (C.ballLipschitz (R+1)) …`, so it already
  bounds `(R+1)`-solutions, exactly the bound the produced `u` (`‖u‖ ≤ R+1`) and Probe 2 at
  `R := R+1` both use.  The vendor's returned window Duhamel form
  (`heatOperator … + ∫ heatKernel (C.apply (timeWindow a T …) …)`) is byte-identical to the
  Duhamel *hypothesis* of Probe 2, so `hloc`'s `hsol` feeds `hinv` directly.
* **Step 2 = one `by_cases` on `t.val ≤ a`.**  `gluePath a b ha hb u v hmatch t` is defeq to
  `glueFunction a b ha hb u v t.val`; `glueFunction_left`/`glueFunction_right` rewrite it to
  `extendPath a ha u t.val` / `extendPath b hb v (t.val-a)`, each defeq to
  `u (projIcc …)` / `v (projIcc …)` (`extendPath = f ∘ projIcc`,
  `Euler/VolterraConvolution.lean:20`), closed by `hu θ _` / `hv θ _`.  `not_le.mp ht |>.le`
  supplies the `a ≤ t.val` side.
* **Step 3 = the vendor induction verbatim + one carried clause.**  Forked
  `EulerBoundedMildContinuation.exists_global_mild_of_bound`
  (`Euler/BoundedMildContinuation.lean:39-83`): same grid (`advance_grid`), same `min δ (S-a)`
  window, same gluing (`gluePath` / `glue_quadratic_mild`), same terminal `subst`.  Added the
  clause `∀ θ t, sobolevTranslation 1 (q+1) (0,θ) (u t) = u t` to the inductive existential.
  Base datum invariance: `ordinarySobolev_angle (q+1) a.toLp a.translation_contDiff` (no
  hypothesis on `a`).  Restart datum invariance: the IH at the restart point (`hinvu θ _`).
  Step invariance: step 1b's clause.  Glue invariance: step 2.  `set u₀ := ordinarySobolev …`
  / `set C := coefficients …` keep the body reading exactly like the vendor's; the vendor
  lemmas take `C`/`u₀` in those slots so unification is by `set`'s defeq.
* **Step 4 = re-assembly, not `apply forced_global_of_bound'`.**  `forced_global_of_bound'`'s
  `hinv` is universally quantified over *all* `R`-bounded solutions on `[0,S]`; discharging it
  outright would need a *global* mild uniqueness on `[0,S]` (chain `mild_solution_unique` along
  the grid), whose one genuinely missing lemma is *restriction of a `[0,S]` Duhamel solution to
  a sub-window* (`REVIEW_A2B.md` §3 last paragraph — the vendor has gluing only, not
  restriction).  Step 3 sidesteps this entirely by producing *one* invariant solution and
  carrying invariance through the construction.  So step 4 obtains that invariant `u` from step
  3 and re-runs `forced_global_of_bound'`'s 4-line assembly (`forced_mild_divergenceFree`,
  `forced_ordinary_descent`) with `hinvu` coming from step 3 rather than from `hinv u hu hm`.
  The conclusion is byte-identical to `forced_global_of_bound'`'s minus the `hinv` premise.

## Heartbeat budget

Only `restart_window_invariance` carries `set_option maxHeartbeats 600000 in` (single
declaration, allowed per `logs/LESSONS.md`; the reviewer bisected `600000` needed, `400000`
fails, `REVIEW_A2B.md` §F6b Probe 2 note).  All four other theorems compile at the default
`200000`.  No heartbeat chasing beyond the reviewer's measured number.

## First-try compile

Both the draft (a throwaway scratch draft (deleted; its content is the module itself — cited by content per LESSONS, not by path), `lake env lean`, exit 0, empty log) and the
real module (`lake build`, 3942 jobs, 5.0 s) compiled on the first attempt.  No failed
approaches at the Lean level: the step decomposition was fixed by the reviewer's checked probes
and the vendor proof, and the `min` simplification (above) removed the only place I had to
choose.  The single non-Lean snag was that `lake env lean` on `axioms_a2b_inv.lean` first
failed with `object file … Euler/OrdinaryCauchyInterpolation.olean … does not exist` — the
four Euler modules the non-vacuity example imports had not been built in this worktree; a
`lake build Euler.OrdinaryCauchyInterpolation Euler.OrdinaryH3Norms Euler.SmoothL2Series
Euler.LpSmoothFieldAlgebra` fixed it (same modules lane 126's audit imports).

## Notes for downstream

* `forced_global_of_bound_unconditional` is the drop-in for A3: it is
  `Continuation.forced_global_of_bound'` with no `hinv`, i.e. the full local-theory shape on the
  prescribed `[0,S]` from `hbound` alone.  A3's remaining job is to *supply* `hbound` (the
  a-priori Sobolev bound), unchanged by this lane.
* Like `Continuation.lean` (see `REVIEW_A2B.md` §F1), this module is imported by nothing in
  `Contracts/`/`Bindings/`/`Tests/`, so it is not in `make test`'s closure until a contract
  consumes it.  Covered here by `research/A01/axioms_a2b_inv.lean`.
