# ATTEMPTS — D-quant, the quantitative finite-order datum constructor (lane 145)

Module `formalization/NSFormalization/Section4/D01/FiniteOrderNorm.lean`
(`#print axioms` = `[propext, Classical.choice, Quot.sound]` for all 16 declarations,
`research/D01/axioms_finite_order_norm.lean`).  Makes `FiniteOrderConstructor.lean`'s
`exists_isSobolevDatum_of_memLp_derivs` quantitative.

## What is proved (positive)

* **D1 — order-0 bound (`c₀ = 1`).**  `norm_orderZeroDatum_le : ‖orderZeroDatum hz‖ ≤ ‖hz.toLp‖`.
  The order-0 realization pipeline is an isometry chain:
  - `cyclesToAngularRealVector 0` is norm-preserving (`cyclesToAngularRealVector_norm_le`,
    `AngularRealVectorBochner.lean:24`, with `frequencyUnit^{|0|}=1`);
  - `𝓕` is Plancherel (`MeasureTheory.Lp.norm_fourier_eq`, isometry);
  - `realProjectionTo 0` is norm-non-increasing (`realProjectionTo_norm_le`, `RealPositiveDensity.lean:41`)
    and here the argument is already conjugate-symmetric, so it is the identity;
  - the componentwise step is the Euclidean-valued `L²` Pythagoras identity
    `‖hz.toLp‖² = ∑ᵢ ‖componentLp hz i‖²` (`norm_toLp_component_sq_sum`), proved here from
    `EuclideanSpace.norm_eq` + `lintegral_finsetSum'` (this is the piece `OrderZeroDatum.lean:40-53`
    records as absent from the tree).
  Bound is `≤` rather than `=` only because the projection/transport factors are stated as `≤ 1` in
  the tree; each is in fact an isometry on the relevant subspace at `s = 0`, so `c₀ = 1` is sharp.

* **D2 — raising bound (`c = 4`).**  `norm_raise_le : ‖A'‖² ≤ 4·(‖A‖² + ∑ⱼ ‖C j‖²)` for the raised
  order-`(s+1)` datum `A'` of `z`, given an order-`s` datum `A` of `z` and, for each `j`, an
  order-`s` datum `C j` of the weak `j`-th derivative.  Ingredients:
  - `coord_smul_deriv_ae` re-derives the a.e. identity `(2πi)·(ξⱼ·(A i)) =ᵐ frequencyUnit·(C j i)`
    from `db_cycles_full` (the transport already inside `memLp_coord_smul_datum`, whose a.e. form is
    not exported);
  - `eLpNorm_coord_smul_eq` reads off `eLpNorm(ξⱼ·(A i)) = eLpNorm(C j i)` (since
    `frequencyUnit = 2π = ‖2πi‖`, the constants cancel);
  - the symbol bound `norm_raiseIntegrand_le` (`FiniteOrderDatum.lean:105`) dominates the raised
    integrand by `‖A i‖ + ∑ⱼ ‖ξⱼ·(A i)‖`; `eLpNorm_add_le` + `eLpNorm_sum_le` give the per-component
    `norm_raiseHilbert_le : ‖raiseHilbert (A i)‖ ≤ ‖A i‖ + ∑ⱼ ‖C j i‖`;
  - a four-term Cauchy–Schwarz `(a+b₀+b₁+b₂)² ≤ 4(a²+b₀²+b₁²+b₂²)` (`nlinarith` on the six
    `sq_nonneg` cross terms) + `PiLp.norm_sq_eq_of_L2` + `Finset.sum_comm` assemble the vector bound.

* **D3 — the quantitative constructor (`c_m = 16^m`).**  `HasWeakDerivsL2Bound z M m` is
  `HasWeakDerivsL2 z m` with the squared `L²` norm of every weak derivative uniformly `≤ M`.
  `exists_isSobolevDatum_norm_le` runs the constructor's induction while carrying the norm: base
  `‖A‖² ≤ M` (D1), step multiplies by `16` (D2 with `∑ⱼ‖C j‖² ≤ 3·16^m·M`), so `c_m = 16^m`.
  `norm_isSobolevDatum_le_of_memLp_derivs` transfers to *any* order-`m` datum by
  `isSobolevDatum_unique`.  `norm_isSobolevDatum_le_two : ‖A‖² ≤ 256·M` is the `m = 2` instance.
  Non-vacuity: `exists_hasWeakDerivsL2Bound_smooth` (every `SmoothL2Field` has a uniform bound to
  every order, via `weakDerivsBound_mono_le`), so the order-2 result is not vacuous.

## Exact shape A3-L1·k needs NEXT (not proved here — do not glue A01 in D01)

A3-L1·k (`research/A01/A3_SPLIT.md:70`) is the `t`-free order-2 norm comparison

    sobolevNormAt 2 (⇑(U t)) ≤ c · ‖u t‖_{SobolevSpace 1 (q+1)}    (c independent of t)

which turns `‖u‖ ≤ ‖u₀‖+1` into `Kbnd := c²·(‖u₀‖+1)²·T₀` for the Grönwall instance
`GronwallInstance.highOrder_bddAbove_of_kbnd` (lane 142).  With lane 145 the chain is:

1. **Norm bridge (A04 ↔ D01, not in this lane).**  `sobolevNormAt 2 (⇑(U t)) = (sobolevENorm 2 (⇑(U t))).toReal`
   (`A04.sobolevNormAt`, `Forcing.lean:74`).  Need `sobolevENorm 2 (⇑(U t)) = ‖A‖` for the order-2
   angular datum `A` of `⇑(U t)` — i.e. identify A04's `sobolevENorm` with the D01 datum norm.  This
   is the "`sobolevNormAt = ‖A‖`" step; it is a *definitional/bridge* obligation on the A04 side, not
   a new analytic fact.  (Vacuity guard: if `sobolevENorm = ⊤` the cap holds trivially with
   `sobolevNormAt = 0`; the point is to make it *non*-vacuous, which needs the datum to exist, i.e.
   step 2.)

2. **`D01.norm_isSobolevDatum_le_two` (lane 145, DONE).**  `‖A‖² ≤ 256·M` for the order-2 datum `A`
   of `⇑(U t)`, given `HasWeakDerivsL2Bound (⇑(U t)) M 2`.  Hence `sobolevNormAt 2 (⇑(U t)) ≤ 16·√M`.

3. **`D-euler-pairing` (the remaining blocker, Euler side, `FINITE_ORDER_SPLIT.md` row D-euler-pairing).**
   Build `HasWeakDerivsL2Bound (⇑(U t)) M 2` with `M ≤ c'·‖u t‖²_{SobolevSpace 1 (q+1)}` (`c'` `t`-free).
   The "free word / lift facts": the mild solution `⇑(U t)` is the lift of `u t`, and its order-≤2
   weak derivatives are the *descended words* whose strong `L²` translation derivatives are
   `C1b-m-E`'s `word_hasDerivAt`; the Schwartz pairing `∫ψ·(∂ⱼz)ᵢ = ∫(-∂ⱼψ)·zᵢ` (the pairing field
   `HasWeakDerivsL2Bound` consumes) follows by parts, and each word's `L²` norm is bounded by
   `‖u t‖_{SobolevSpace 1 (q+1)}` (`q ≥ 1 ⇒ q+1 ≥ 2`, so `H^{q+1} ↪ H²` controls the order-≤2 data).
   Then `c := 16·√c'` is the `t`-free constant of A3-L1·k.

So lane 145 discharges the **norm-comparison half** (steps 1-side inequality + 2); the residual for
A3-L1·k is the **A04 norm bridge** (step 1 identification) and **D-euler-pairing** (step 3), both
outside D01.  The old "raising is unbounded on `L²`, no CLM to bundle" obstruction
(`C1B_SPLIT.md` C1b-c8-m) does **not** block the *bound*: `norm_raiseHilbert_le` controls the raised
norm through `coord_smul_deriv_ae`, not through operator-norm bundling.

## Negative / discarded approaches

* **`c₀ = √3` via `PiLp.norm_apply_le` (component ≤ full norm).**  Bounding each `‖componentLp hz i‖ ≤
  ‖z‖_{L²}` and summing gives `‖v‖ ≤ √3·‖z‖`, avoiding the Pythagoras identity — but it is not sharp
  and hides that the pipeline is an isometry.  Discarded in favour of the exact identity
  `norm_toLp_component_sq_sum` (`c₀ = 1`).
* **Extracting the a.e. identity from `memLp_coord_smul_datum` directly.**  Its internal `heq` (the
  a.e. equality) is not exported (the lemma returns only `MemLp`), and cannot be recovered from the
  `MemLp` conclusion.  Re-deriving the ~35-line transport as `coord_smul_deriv_ae` was necessary; the
  body is the same substitution of `db_cycles_full` through the dilation/weight factors.
* **`rw [Lp.norm_toLp]` on `‖raiseHilbert‖`.**  Fails: `hgi : RaisableWitness (A i)` is a `def`
  wrapping `MemLp`, so the `‖MemLp.toLp _ ?hf‖` pattern does not unify at `rw`'s reducible
  transparency (`RaisableWitness` not unfolded).  Fix: `exact Lp.norm_toLp _ hgi` (term mode unfolds
  the def).  Likewise a function-level `set Ai := (fun ξ => …)` makes the same `rw` motive ill-typed;
  keep `set` at the Lp-element level only.
* **`gcongr with j` for `4·(a+∑) ≤ 4·(a'+∑')`.**  Presents the split goals in an order that does not
  match `[a-goal, sum-goal]`; replaced by explicit `mul_le_mul_of_nonneg_left` + `add_le_add … Finset.sum_le_sum`.

## Missing file

`research/A01/REVIEW_EULER_PAIRING.md` (the brief's "A3-L1·k answer" pointer) is **absent from this
worktree** (base `origin/erenup/integration`).  The D-euler-pairing shape recorded above is
reconstructed from `research/A01/A3_SPLIT.md` (row A3-L1·k) and `research/A01/C1B_SPLIT.md`
(rows C1b-m-E, C1b-c8-m).  If that review file exists on integration/main, its "free word/lift"
statement should be cross-checked against step 3 above (lead to reconcile).
