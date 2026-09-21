# R42 item 1f — `pressure_gradient` for `p_ε = π + P_ε` (lane 083)

Module: `formalization/NSFormalization/Section4/R42/PressureGradient.lean`
(imports only `NSFormalization.Section4.A02.SolutionClass` + Mathlib).

## What was built

Three public declarations (+ one helper), all axioms
`[propext, Classical.choice, Quot.sound]`:

* `contDiff_slice_pressure` — helper: the spatial slice `x ↦ p(t,x)` of a field
  `ContDiffOn ℝ ∞` on the closed-at-zero slab `Ico 0 T ×ˢ univ` is `ContDiff ℝ ∞`
  for `t ∈ Ico 0 T`.  Byte-identical inline copy of `D01/DatumToJets.lean:377`
  `contDiff_slice_scalar`.  Route: `rw [← contDiffOn_univ]`, compose with the affine
  inclusion `x ↦ (t,x)` via `ContDiffOn.comp`, preimage subset from `t ∈ Ico 0 T`.
  Named with the `_pressure` suffix (review finding 2): the unqualified name
  `contDiff_slice` is D01's **vector** lemma (`v : ℝ × Space → Space`), so a module
  opening both `NSFormalization.Section4.D01` and this namespace would get an
  ambiguous `contDiff_slice`; `contDiff_slice_pressure` (or D01's
  `contDiff_slice_scalar`) avoids the clash.

  **Why inline rather than `import D01.DatumToJets`** (review-measured, finding 4):
  local-module transitive closures are `A02.SolutionClass` 50, this module as
  committed 51, `D01.DatumToJets` 597 — so importing `DatumToJets` would take this
  module from 51 to 599 local modules (**+548**, an 11× blowup on top of a much
  larger Mathlib surface) to reuse a 10-line helper.  Inlining follows the repo's own
  precedent (`A02/SolutionClass.lean:44-50` refuses the D01 import for the same
  reason).  If the *assembly* module ends up importing D01 anyway (its siblings
  already pull `D01.ForceClass`, and `DatumToJets` adds only +2 on top of
  `R42.CorrectionPath`'s closure), a later lane could drop this copy.
* `memLp_pressureGradient_of_compact` (Lemma 1, S–M).
* `memLp_pressureGradient_add` (Lemma 2, S).
* `memLp_pressureGradient_of_difference_support` (corollary the consumer calls).

## Exact Mathlib names used (this rev, v4.34.0-rc2)

* `ContDiff.continuous_fderiv : ContDiff 𝕜 n f → n ≠ 0 → Continuous (fderiv 𝕜 f)`
  — note the side condition is `n ≠ 0`, NOT `1 ≤ n`.  With `n = ∞` discharged by
  `by decide` (`(∞ : ℕ∞ω) ≠ 0`).
* `ContDiff.differentiable : ContDiff 𝕜 n f → n ≠ 0 → Differentiable 𝕜 f` — same
  `n ≠ 0` side condition, again `by decide`.
* `Filter.EventuallyEq.fderiv_eq : f₁ =ᶠ[𝓝 x] f → fderiv 𝕜 f₁ x = fderiv 𝕜 f x`.
* `image_eq_zero_of_notMem_tsupport : x ∉ tsupport f → f x = 0`.
* `isClosed_tsupport`, `IsOpen.mem_nhds`, `HasCompactSupport.of_support_subset_isCompact`,
  `isCompact_closedBall`, `Metric.ball_subset_closedBall`.
* `continuous_finsetSum` (NOT `continuous_finset_sum`, which is deprecated),
  `Continuous.clm_apply`, `Continuous.smul`, `Continuous.memLp_of_hasCompactSupport`.
* `fderiv_add`, `add_apply` (NOT `ContinuousLinearMap.add_apply`, deprecated),
  `add_smul`, `Finset.sum_add_distrib`, `MemLp.add`.

## Failed / adjusted approaches (recorded)

1. `hq.continuous_fderiv (le_top)` and `hπq.differentiable le_top` — WRONG side
   condition.  Both lemmas want `n ≠ 0`, not `1 ≤ n`; `le_top` has type
   `_ ≤ ⊤` and does not typecheck as `∞ ≠ 0`.  Fix: `by decide`.
2. `filter_upwards [...] with y hy; exact image_eq_zero_of_notMem_tsupport hy` —
   the elaborator unified `f := P` and `x := (t,y)`, expecting `(t,y) ∉ tsupport P`
   (wrong `f`).  Fix: pin `(f := fun x : Space => P (t, x))`.
3. `rw [hz.fderiv_eq, fderiv_const]; rfl` — `fderiv_const` is stated for
   `Function.const E c`, but after `hz.fderiv_eq` the goal carries the anonymous
   `fun _ => 0`, so `rw [fderiv_const]` finds no occurrence.  Fix: `rw [hz.fderiv_eq]; simp`
   (simp closes `fderiv ℝ (fun _ => 0) x = 0`).
4. ~~In the corollary, rewriting `p` into `π + (p − π)` with a hypothesis
   `p = fun z => π z + (p z − π z)` loops: `rw` replaces every `p`, including the
   `p` inside the RHS.~~  **RETRACTED (review finding 1 — this was FALSE).**  The
   reviewer reproduced the "failing" form verbatim and it compiles with no error and
   no warning; the `simp only`-driven variant reports `simp made no progress`, not a
   loop.  What actually happened: no loop was ever *observed* — I predicted one by
   reasoning, and the reasoning was wrong on two counts.  (i) `rw` substitutes into
   the **goal** only; it does not re-rewrite the `p` it just introduced from the RHS.
   (ii) The corollary's goal is `MemLp (fun x => pressureGradient p t x) 2 volume`,
   which contains `p` **once** (the pressure argument); the multi-`p` situation I
   pictured belonged to a different, intermediate goal shape
   (`pressureGradient p t x = pressureGradient (…) t x`, `p` on both sides) that the
   direct proof never creates.  So `heq : p = fun z => π z + (p z − π z)` with a
   single `rw [heq]` is safe and correct.  **Fix applied**: the corollary tail is now
   the 3-line direct form

   ```lean
   have heq : p = (fun z : ℝ × Space => π z + (p z - π z)) := by funext z; ring
   rw [heq]
   exact hadd
   ```

   (`exact hadd` closes the residual beta-redex `(fun z => p z − π z) z` vs
   `p z − π z` by defeq), replacing the earlier five-line `heq`-reversed +
   `hgoal` + `rw [← hgoal]` detour, which — though it also compiled — was
   motivated by the wrong prediction above.
5. For Lemma 2's pointwise identity, `unfold pressureGradient` leaves the
   beta-redex `(fun z => π z + P z) (t,y)`; `simp only [pressureGradient]`
   beta-reduces it to `π (t,y) + P (t,y)`, which then matches `fderiv_add`'s LHS
   after `rw [← Finset.sum_add_distrib]` + `Finset.sum_congr rfl`.

## Consumer note (assembly glue, review-verified end to end — finding 3)

`memLp_pressureGradient_of_difference_support` is the `pressure_gradient` field of
`ClassicalSolutionR` for `p_ε = π + P_ε`.  The reviewer compiled the full assembly
step against the real contract (`/tmp/r42rev/consume.lean`, 0 errors): from
`F : InsertionFamilyAPI ν Pk`, `ε ∈ Ioc 0 F.ε₀`, `0 < S < F.scaling.correction.T`,
it produces `∀ t ∈ Ico 0 S, MemLp (pressureGradient (F.pressure ε) t ·) 2 volume`
with no extra hypotheses.  About ten mechanical lines.  Because the lemmas are stated
about **bare functions** (not either copy of the structure), the same corollary serves
`Contracts.V1.Data.ClassicalSolutionR` and `A02.ClassicalSolutionR` with no transport.

Instantiate the lemma's `T` at `F.scaling.correction.T` (NOT at `S`).  Then, at each
`t ∈ Ico 0 S`:

* `hp` = `F.pressure_smooth ε hε` — **verbatim**, already on `Ico 0 T`
  (`InsertionFamily.lean:200`).
* `hsupp` = `F.pressureDifference_support ε hε t htT` — **verbatim**
  (`InsertionFamily.lean:255`).
* `ht` — widen `t ∈ Ico 0 S` to `Ico 0 T` (and to `Ico 0 (T+δ)`) by
  `Ico_subset_Ico_right`, using `margin_pos : 0 < δ` (`Correction.lean:207`). ~2 lines.
* `hπ` — **three** lines, not one: `F.reference.pressure_smooth` is on `Ico 0 (T+δ)`
  about `reference.pressure`, so `rw [F.reference_pressure] at this` then
  `this.mono (Set.prod_mono (Ico_subset_Ico_right (by linarith)) subset_rfl)`.
* `h1` — two lines: `F.reference.pressure_gradient t htTδ` then `rwa [F.reference_pressure]`.

**Trap for the assembly lane** (would cost a session if hit): π's smoothness MUST be
taken from `InsertionFamilyAPI.reference.pressure_smooth` (the `Data.ClassicalSolutionR`
field, on the **half-open** `Ico 0 (T+δ)`), **not** from
`CorrectionAPI.reference_pressure_smooth`, which lives on the **open** slab
`Ioo 0 (T+δ)` (`Correction.lean:226`, flagged in `InsertionFamily.lean:53-54`) and so
cannot reach `t = 0` — exactly the point `Ico` needs.
