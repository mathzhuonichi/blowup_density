# ATTEMPTS — lane 125 (C1b-m-D, the finite-order datum constructor)

Non-generated notes for `Section4/D01/FiniteOrderDatum.lean`.  Probes:
`research/D01/probes/{finite_order_probe,raise_probe,raise_probe2,raise_probe3,bound_probe2,witness_probe}.lean`.

## Decision on scope / hypothesis shape

The full induction step (d) — "order-`m` datum of `z` and of each `∂ⱼz` (as `L²` fields) ⟹
order-`(m+1)` datum of `z`" — is **blocked on the raw-frequency Fourier identity** (row D-b):
`(ξ j)·(A i) =ᵐ c·(datum of ∂ⱼz)ᵢ` at the a.e. *coeFn* level.  The tree has that identity only in
operator/distribution form (`Paper3.angularRealization_directionalDerivative`,
`DerivativeDatum.lean:69`, which is smoothness-free but lifts to distributions, not to a raw
multiplier) and, for `isSobolevDatum_partialDeriv`, only for a `SmoothL2Field`.

So per the brief's fallback, I stated the induction step with the analytic content packaged as an
**explicit `L²` witness** `RaisableWitness (A i) := MemLp (ξ ↦ (1+‖ξ‖²)^{1/2}·(A i)(ξ)) 2 volume`,
which **is** dischargeable today (`isSobolevDatum_raise`), and I additionally proved
`raisableWitness_of_memLp_smul` (reduces the witness to coordinate `L²`) and the symbol bound (c).
The gap between my hypothesis shape and (d)'s "datum of `∂ⱼz`" shape is **exactly** D-b — recorded
sharply in `FINITE_ORDER_SPLIT.md`.

Key structural facts found while probing (informed the design):
* The **realization identity** `angularRealization (s+1) (raiseHilbert a hg) = angularRealization s a`
  does **not** need reality of `a` (probe `raise_probe2.lean`: the `hh` hypothesis was flagged
  unused).  Reality is only needed to land the raised element in `realSubspace`.
* `realSubspace` ignores its order argument (`RealSobolev.lean:118`), so `realSubspace (s+1)` and
  `realSubspace s` are defeq; the membership proof transports without an order coercion.
* The order lowering `angularOrderLowering (s+1) s` is, in the raw variable, exactly multiplication
  by `sobolevBesselWeight (-1)` (`Leray.angularOrderLowering_coeFn'`), and
  `sobolevBesselWeight (-1) · sobolevBesselWeight 1 = sobolevBesselWeight 0 = 1`
  (`sobolevBesselWeight_mul`), so raising is an exact right inverse of lowering on its domain.
* Existence needs **no** vector Plancherel isometry (the item `OrderZeroDatum.lean:40-53` flags as
  absent); the `isSobolevDatum_raise` proof carries no norm.

## Failed / corrected approaches (exact errors)

1. **`fun_prop` cannot prove the weight continuous.**  `unfold sobolevBesselWeight; fun_prop` gave
   ```
   `fun_prop` was unable to prove `Continuous fun ξ => ↑((1 + ‖ξ‖ ^ 2) ^ (1 / 2))`
   Issues: Failed to prove necessary assumption `0 ≤ 1 / 2` when applying theorem
   `Real.continuous_rpow_const`.
   ```
   Fix: `refine Complex.continuous_ofReal.comp (Continuous.rpow_const ?_ ?_)` with the base branch
   `fun_prop` and the side condition `intro ξ; exact Or.inl (by positivity : (0:ℝ) < 1+‖ξ‖^2).ne'`
   (use the `f x ≠ 0` disjunct, base is strictly positive).

2. **`Real.rpow_natCast` is the wrong rewrite for `√ = ^(1/2)`.**  In `norm_sobolevBesselWeight_one`,
   ```
   rewrite failed: Did not find an occurrence of the pattern `?x ^ ↑?n`
   in ... (1 + ‖ξ‖ ^ 2) ^ (1 / 2) = √(1 + ‖ξ‖ ^ 2)
   ```
   Fix: `Real.sqrt_eq_rpow` (rewrites `√x` to `x ^ (1/2 : ℝ)`), after `Complex.norm_real`,
   `Real.norm_eq_abs`, `abs_of_nonneg (by positivity)`.

3. **`memLp_finset_sum'` deprecated and mis-unifies.**  Building `MemLp F 2` with
   `apply memLp_finset_sum'` gave both a deprecation (→ `memLp_finsetSum'`) and
   ```
   could not unify ... MemLp (∑ i ∈ ?s, ?f i) ?p ?μ  with  MemLp (fun ξ => ∑ j, ‖…‖) 2 volume
   ```
   (the lemma wants a `Finset.sum` of functions, not a `fun ξ => ∑ …`).  Fix: `Fin 3` is concrete,
   so `simp only [Fin.sum_univ_three]` then `((hcoord 0).norm.add (hcoord 1).norm).add (hcoord 2).norm`.

4. **`← add_mul` did not fire** in `norm_raiseIntegrand_le`: after `← Finset.sum_mul` the goal was
   `√(1+‖ξ‖²)·‖hξ‖ ≤ ‖hξ‖ + (∑|ξi|)·‖hξ‖`, with no `?a*?c + ?b*?c` pattern (the `‖hξ‖` summand is
   not written as `1·‖hξ‖`).  Fix: take
   `h1 := mul_le_mul_of_nonneg_right (sqrt_one_add_normSq_le ξ) (norm_nonneg _)` and
   `rwa [add_mul, one_mul] at h1`.

5. **Namespace of the order-lowering coeFn.**  `Leray.angularOrderLowering_coeFn'` is unknown unless
   `NSFormalization.Section4.D01` is open; either open `NSFormalization.Section4.D01.Leray
   (angularOrderLowering_coeFn')` or use the full path.  (In the module the enclosing namespace is
   `NSFormalization.Section4.D01`, so the explicit `open … Leray (…)` is used.)

## Post-review (lane-125 review, `research/D01/REVIEW_FINITE_ORDER.md`, ACCEPT-WITH-NOTES)

* **`sqrt_one_add_normSq_le` simplified (review finding 4), statement unchanged.**
  Before (16 lines): `EuclideanSpace.norm_eq` + `Real.sq_sqrt` to get `‖ξ‖² = ∑(ξj)²`, then
  `∑(ξj)² ≤ (∑|ξj|)²` by `Fin.sum_univ_three` + `nlinarith` on the cross-term products, then
  `Real.sqrt_le_sqrt` after squaring the RHS.
  After (3 lines):
  ```lean
  (sqrt_one_add_norm_sq_le ξ).trans (by gcongr; exact EulerMeanCutoffCurl.norm_le_sum_coordinates ξ)
  ```
  Mathlib `sqrt_one_add_norm_sq_le` (`Analysis/SpecialFunctions/JapaneseBracket.lean:41`) gives
  `√(1+‖ξ‖²) ≤ 1+‖ξ‖`; tree `EulerMeanCutoffCurl.norm_le_sum_coordinates` gives `‖ξ‖ ≤ ∑ⱼ‖ξ.ofLp j‖`
  (= `∑ⱼ|ξ j|` for real coords, closed by `gcongr` + `exact`, defeq on `‖·‖=|·|`).  Verified: the
  3-line proof compiles with standard axioms (reviewer `/tmp/rev125/p6_simp.lean`; re-checked here).
  Neither lemma name was known to me during the lane; found by the reviewer via `exact?`.

* **Reviewer probes preserved** under `research/D01/probes/rev125_*.lean` (verbatim, credited in
  headers), each compiles under `lake env lean`: `rev125_partialderiv_weak.lean`,
  `rev125_db_cycles.lean`, `rev125_nonvac.lean` (carries the expected `iteratedFDeriv_zero_fun`
  deprecation warning, exit 0), `rev125_collapse.lean`, `rev125_converse.lean`.  These establish that
  the split table's row D-b is only an **M** (the raw multiplier `sobolevDirectionalDerivative_coeFn`
  is in tree; only the cycles→angular transport `memLp_coord_smul_datum` is new) and that the
  `SmoothL2Field` hypothesis of `isSobolevDatum_partialDeriv` is removable in 10 lines by
  Schwartz duality.  `axioms_finite_order.lean` extended to all 11 exports (review finding 1).

## Gates (all from `verification/`, `LEAN_NUM_THREADS=6`, after `. scripts/lean-env.sh`)

* `lake build NSFormalization.Section4.D01.FiniteOrderDatum` — `Build completed successfully (9928 jobs).`
* `lake env lean ../formalization/NSFormalization/Section4/D01/FiniteOrderDatum.lean` — silent.
* `lake env lean ../research/D01/axioms_finite_order.lean` — every decl
  `depends on axioms: [propext, Classical.choice, Quot.sound]`.
* `make check` (from worktree root) — 13 tests OK; 30 work items consistent.
