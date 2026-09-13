# A04 unit G1 — sub-lemma SL3, step 1: skew-adjointness of `angularDirectionalDerivative`

Lane 076, task A04, step 1 of the SL3 route recorded in lane 066
(`research/A04/ATTEMPTS_SL3.md` §"What remains", and the end docstring of
`Section4/A04/LaplacianDatum.lean`).  One bounded unit: prove that the angular
directional-derivative operator is `L²`-skew-adjoint.  New module
`formalization/NSFormalization/Section4/A04/LaplacianPairing.lean`.

## Deliverable (compiles, `sorry`-free, standard axioms only)

```
theorem NSFormalization.Paper3.inner_angularDirectionalDerivative_right
    (s : ℝ) (a : Space) (f g : Lp ℂ 2 (volume : Measure Space)) :
    ⟪f, angularDirectionalDerivative s a g⟫_ℂ = -⟪angularDirectionalDerivative s a f, g⟫_ℂ
```

Companion (same technique, real symbol → no minus sign; **required by step 3**, see §"What still
remains"):

```
theorem NSFormalization.Paper3.inner_angularOrderLowering
    (s r : ℝ) (hrs : r ≤ s) (f g : Lp ℂ 2 (volume : Measure Space)) :
    ⟪f, angularOrderLowering s r hrs g⟫_ℂ = ⟪angularOrderLowering s r hrs f, g⟫_ℂ
```

## The carrier and how its inner product unfolds (requested)

`angularDirectionalDerivative s a : Lp ℂ 2 volume →L[ℂ] Lp ℂ 2 volume` is stated directly on
`Lp ℂ 2 (volume : Measure Space)` (there is no `RealSobolevHilbert`/`FourierData` wrapper here —
`SobolevHilbert s` is `abbrev … := Lp ℂ 2 volume`, `SobolevHilbertModel.lean:21`).  So the
relevant inner product is the plain `L²` inner product on `Lp ℂ 2 volume`:

* `⟪f, g⟫_ℂ  =  @inner ℂ (Lp ℂ 2 volume) _ f g`  (notation from `open scoped InnerProductSpace`,
  `⟪x, y⟫_𝕜 := inner 𝕜 x y`, Mathlib `Analysis/InnerProductSpace/Defs.lean:86`).
* `MeasureTheory.L2.inner_def` (which is `rfl`): `⟪f, g⟫ = ∫ ξ, ⟪f ξ, g ξ⟫ ∂volume`, where the
  integrand is the scalar inner product `@inner ℂ ℂ _ (f ξ) (g ξ)`.
* `RCLike.inner_apply` (`@[simp]`, `rfl`): on the scalar field `⟪z, w⟫ = w * conj z`.  **Note the
  orientation: second argument times `conj` of first** (`RCLike.inner_apply'` is the swapped
  `conj z * w`).  This orientation is what makes the pointwise algebra come out; it is easy to get
  the sign/order wrong here.

So skew-adjointness is literally: `∫ ξ, (M y) ξ * conj (x ξ) = -∫ ξ, (M x) ξ * conj (y ξ)`, i.e.
the symbol satisfies `conj σ = -σ` pointwise.

## Route as executed

`angularDirectionalDerivative s a = U ∘ M_s ∘ U⁻¹`, exactly as the lane-066 docstring prescribed:

* `U = Paper3.angularFrequencyDilation`, a `≃ₗᵢ[ℂ]` (unitary) on `Lp ℂ 2 volume`
  (`AngularFourierDilation.lean:80`).
* `M_s = angularWeightEquiv (s-1) ∘ sobolevDirectionalDerivative s a ∘ (angularWeightEquiv s).symm`
  — the new local def `angularDirectionalMid`.  This is a genuine multiplication operator; its a.e.
  coefficient is the three-way symbol product
  `angularWeightSymbol (s-1) ξ * sobolevDirectionalSymbol a ξ * angularWeightSymbol (-s) ξ`
  (`angularDirectionalMid_coeFn`, from the three existing `_coeFn` lemmas).

Steps:

1. **Factoring is definitional.**  `angularDirectionalDerivative_eq_dilation_mid : … = rfl`.
   Because `cyclesToAngular s = (angularWeightEquiv s).trans angularFrequencyDilation`
   (`AngularTameProduct.lean`), and `angularDirectionalDerivative` is
   `cyclesToAngular (s-1) ∘ sobolevDirectionalDerivative s a ∘ (cyclesToAngular s).symm`, peeling
   `U` off the outside and `U⁻¹` off the inside leaves precisely `M_s`.  The only non-obvious defeq
   is `(cyclesToAngular s).symm h`'s inner dilation factor being `angularFrequencyDilation.symm h`
   (the `≃ₗᵢ` symm, not the `≃L` symm): this is `rfl` because
   `LinearIsometryEquiv.toContinuousLinearEquiv_symm` (Mathlib `LinearIsometry.lean:675`) is `rfl`.
   Verified: the whole factoring closes by `rfl`.
2. **Skew-adjointness of `M_s`** (`inner_angularDirectionalMid`): `L2.inner_def` on both sides,
   `← integral_neg` to pull the sign under the integral, `integral_congr_ae`, then a pointwise
   `filter_upwards` with the two `angularDirectionalMid_coeFn`s.  After `simp only [RCLike.inner_apply,
   hy, hx]` the goal is `(σ ξ * y ξ) * conj (x ξ) = -(y ξ * conj (σ ξ * x ξ))`; `rw [map_mul,
   mid_symbol_imaginary]` (turning `conj (σ ξ * x ξ)` into `conj σ ξ * conj (x ξ)` then
   `conj σ ξ = -(σ ξ)`) and `ring` close it.
3. **Transport across `U`** (`inner_angularDirectionalDerivative_right`): a 5-line `calc` using
   `LinearIsometryEquiv.inner_map_map` (`⟪U x, U y⟫ = ⟪x, y⟫`) and
   `LinearIsometryEquiv.apply_symm_apply` (`U (U⁻¹ x) = x`).  Write `f = U (U⁻¹ f)`, apply
   `inner_map_map` to drop both `U`s, apply step 2, then re-insert `U` on both slots and fold back.
   **No dilation coefficient function is used** (confirmed: there is none in tree and none is needed).

The lowering companion (`angularOrderLoweringMid`, `…_coeFn`,
`inner_angularOrderLoweringMid`, `inner_angularOrderLowering`) is identical, with
`sobolevOrderLowering_coeFn` in place of `sobolevDirectionalDerivative_coeFn` and
`lowering_symbol_real` (`conj σ = σ`) in place of `mid_symbol_imaginary`; no `integral_neg`, no
minus sign.

## Pitfalls anticipated and designed around (negative examples)

These are hazards I read out of the source lemmas and lane-066 notes and avoided by construction;
none produced a compile failure because the proof was written against them from the start.

* **`RCLike.inner_apply` returns `w * conj z`, not `conj z * w`.**  The `@[simp]` normal form
  (`Analysis/InnerProductSpace/Basic.lean:911`) puts the second argument first.  Writing the
  pointwise goal with the wrong order makes the final `ring` need the imaginarity fact applied to
  the wrong factor.  Kept the algebra generic (`ring`) so the exact orientation is irrelevant once
  `conj σ = ±σ` is in hand.
* **Do NOT `simp only [map_mul]` on the conjugated symbol.**  `σ ξ` is itself the product
  `A*B*C`; a blanket `map_mul` expands `conj (A*B*C)` into `conj A * conj B * conj C`, and then
  `mid_symbol_imaginary`/`lowering_symbol_real` (stated with `conj` of the *whole* product) no
  longer matches.  Used a single `rw [map_mul, …]`, which peels only the outer
  `conj ((A*B*C) * x ξ) = conj (A*B*C) * conj (x ξ)` and leaves `conj (A*B*C)` intact for the
  symbol lemma.  (This is the one `conj (_*_)` subterm in the goal — `conj (x ξ)` is not a product —
  so the single `rw` targets it unambiguously.)
* **`M_s` is a multiplication operator; `U` is a change of variables.**  Skew-adjointness must be
  proved on `M_s` (where `L2.inner_def` + a symbol identity works) and then *transported* through
  the isometry `U`; there is deliberately no attempt to compute a coefficient function for `U`
  (the lane-066 first draft's rejected idea).
* **`(angularWeightEquiv s).symm k = angularWeightEquiv (-s) k` by `rfl`.**  Verbatim from
  `angularWeightEquiv_symm_apply` (`Paper3/AngularSobolevCoordinates.lean:288`,
  `@[simp] … := rfl`).  Both sides further unfold to `angularWeightMap (-s) k` (the forward map of
  the equiv *is* `angularWeightMap`), which is what lets the inner factor's coeFn in
  `angularDirectionalMid_coeFn` be `angularWeightMap_coeFn (-s) y` *type-ascribed* onto
  `((angularWeightEquiv s).symm y : Space → ℂ)` so the `rw` chain lines up syntactically; likewise
  the outer factor's coeFn is `angularWeightMap_coeFn (s-1) _` ascribed onto
  `angularDirectionalMid s a y` (the `.comp` / `toContinuousLinearMap` /
  `angularWeightEquiv = angularWeightMap` defeqs all hold, so the ascription typechecks).

## What still remains (the SL3 gap after this unit) — corrected per review (F1, F2)

Delivered here: step 1 (directional-derivative skew-adjointness `inner_angularDirectionalDerivative_right`)
and step 2 (order-lowering self-adjointness `inner_angularOrderLowering`) of the route.  **Both are
required for step 3** — step 2 is *not* an optional bonus (see below).  Step 3 is not widened into
this lane, per the task scope; it is re-sized to **M** (not S) below.

### Step 3 — Laplacian datum assembly *and* datum-order reconciliation (size M)

The lane-066 briefing said `mid_symbol_order_independent` (`D01/DerivativeDatum.lean:207`)
collapses the `m/m+1/m+2` bookkeeping.  **That is wrong, and it is the crux of what remains.**
`mid_symbol_order_independent` equalizes only the **operator** index — it says every
`angularDirectionalDerivative s a` has the *same symbol*, i.e. is the same map.  It says nothing
about the **datum** index: `datum_m u`, `datum_{m+1} u`, `datum_{m+2} u` are genuinely *different*
elements of `Lp ℂ 2 volume` (they differ by a Bessel weight — that is exactly why
`angularRealization s` depends on `s`).  Running the plan through:

* assembly (the plan): `datum_m(Δu) = ∑ⱼ D_j (D_j (datum_{m+2} u))`, from
  `isSobolevDatum_partialDeriv` (twice, via `partialDeriv j Z.field = (Z.directionalField eⱼ).field`)
  + `D01.isSobolevDatum_add` over the three directions;
* with `G = datum_m u`, this lane's skew-adjointness gives
  `⟪G, datum_m(Δu)⟫ = -∑ⱼ ⟪D_j (datum_m u), D_j (datum_{m+2} u)⟫`;
* but the RHS already in tree, `A04.gradientSobolevENorm_toReal_sq_eq_datum_sum`
  (`LaplacianDatum.lean:130`), is `∑ⱼ ‖D_j (datum_{m+1} u)‖²`.

So there is a missing reconciliation step (with `v = ∂ⱼu`):
`⟪datum_{m-1} v, datum_{m+1} v⟫ = ‖datum_m v‖²`, i.e. `⟪Λ⁻¹w, Λw⟫ = ‖w‖²` for the real positive
lowering multiplier `Λ`.  **This is precisely what `inner_angularOrderLowering` is for** —
hence step 2 is a required input, not optional.  Pieces the step-3 lane needs:

* `inner_angularOrderLowering` (this lane) — the `⟪Λ⁻¹w, Λw⟫ = ‖w‖²` pairing (self-adjointness of
  the lowering, applied with `Λ` and `Λ⁻¹` at the two orders).
* `D01.isSobolevDatum_unique` (`D01/ForceClass.lean:286`) — to say `datum_m u` *is* the lowering of
  `datum_{m+1} u`, not merely *a* datum.
* `A03.lowerDatum` / `A03.coe_lowerDatum` (`A03/RealAngularProduct.lean:140`, `:144`) and
  `A03.IsScalarSobolevDatum.lower` (`A03/ScalarTameProduct.lean:114`) — the order-lowering datum
  fact (scalar form; a `RealVectorSobolev` analogue is a componentwise wrapper via
  `A03.isSobolevDatum_iff`, `A03/VectorTameProduct.lean:54`).
* **Not in tree, must be written (≈3 lines from `Paper3.weight_product_order_indep`,
  `D01/DerivativeDatum.lean:192`):** an order-independence lemma for the *lowering* middle symbol —
  `angularWeightSymbol r · sobolevBesselWeight (r-s) · angularWeightSymbol (-s)` depends only on
  `r - s` — or, equivalently, a commutation
  `angularDirectionalDerivative ∘ angularOrderLowering = angularOrderLowering ∘ angularDirectionalDerivative`.
  This is the genuinely new analytic content of step 3.

### The real vs complex inner product (F2 — the `re` step is neither definitional nor tooled)

This lane's theorems are on the **complex** inner product of `Lp ℂ 2 volume`.  But `hlap` is
consumed by `A04.inner_energy_assembly` (`A04/HighEnergy.lean:101-110`), stated over
`[InnerProductSpace ℝ E]` at `E = RealVectorSobolev m`, i.e. the **real** inner product.  The
instance path is:

`InnerProductSpace ℝ (RealVectorSobolev s)` = `PiLp.innerProductSpace` (`Fin 3` product) over
`Paper3.realSobolevInnerProductSpace s` (`Paper3/RealPositiveDensity.lean:27`) =
`Submodule.innerProductSpace` on `(realSubspace s).toSubmodule`, which sits in `Lp ℂ 2 volume` with
`MeasureTheory.L2.innerProductSpace` **at `𝕜 = ℝ`** (`∫ ⟪f ξ, g ξ⟫_ℝ`).

Crucially this is **not** `Inner.rclikeToReal ℂ`.  Consequences the step-3 lane must respect
(both confirmed by the reviewer's probes):

* `(inner ℝ x y : ℝ) = RCLike.re (inner ℂ x y)` on `Lp ℂ 2 volume` is **not** `rfl`;
* `real_inner_eq_re_inner` (Mathlib `InnerProductSpace/Basic.lean:959`) does **not** apply — it is
  stated for `Inner.rclikeToReal 𝕜`, and Lean reports the instance mismatch against the `L2` one.

Nothing in tree bridges the real and complex inner products on an `Lp`/datum carrier (grep over
`Section4/` finds no such lemma).  Two routes:

1. keep this lane's complex theorems and cross with `MeasureTheory.integral_re`
   (`.../Integral/Bochner/ContinuousLinearMap.lean:164`) + an integrability side condition, to
   move `re` through the integral; **or**
2. **(recommended)** re-prove skew-adjointness *directly* on `angularDirectionalDerivativeReal`
   (`D01/DerivativeDatum.lean:134`) using the **real** `L2.inner_def` and the same pointwise symbol
   argument.  On `RealSobolevHilbert` the inner product restricts to the ambient real `L²` inner
   (`Submodule` inner), and `angularDirectionalDerivativeReal_coe` (`:141`, `rfl`) sends the
   coercion straight to `angularDirectionalDerivative`, so the identical `filter_upwards` +
   `RCLike.inner_apply` (over `ℝ`) + `mid_symbol_imaginary` argument closes **without ever swapping
   `re` and `∫`** (both sides stay under one real integral).  This is arguably the statement this
   lane should have delivered; it removes the F2 bridge entirely, at the cost of restating the two
   theorems on the real carrier.  The complex versions here are still reusable via route 1 if
   preferred.

The final `hlap` then combines the reconciliation, this adjointness, the `PiLp 2` componentwise
sum, and `A04.gradientSobolevENorm_toReal_sq_eq_datum_sum` (`≤` suffices; `inner_energy_assembly`
weakens with `0 ≤ ν`).

## Commands run

- `cd verification && lake build NSFormalization.Section4.A04.LaplacianDatum NSFormalization.Section4.D01.DerivativeDatum`
  → `Build completed successfully (9891 jobs)` (dependency sanity).
- `cd verification && lake build NSFormalization.Section4.A04.LaplacianPairing`
  → `Built NSFormalization.Section4.A04.LaplacianPairing (4.4s)` / `Build completed successfully (9892 jobs)`.
- `cd verification && lake env lean ../formalization/NSFormalization/Section4/A04/LaplacianPairing.lean`
  → empty output, exit 0 (zero warnings, default heartbeat budget, no `set_option`).
- `cd verification && lake env lean ../research/A04/axioms_sl3_pairing.lean`
  → all 10 public declarations depend only on `[propext, Classical.choice, Quot.sound]`.
- `make check` (worktree root) → exit 0.
