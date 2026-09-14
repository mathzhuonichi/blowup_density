# A04 unit G1 — sub-lemma SL3, step 3a: the real-carrier pairing identities

> **Lane 123 (MAINT, 2026-09-13):** this module was relocated to `formalization/NSFormalization/Section4/D01/RealPairing.lean` (namespace `NSFormalization.Paper3` unchanged; only the `import` of the sibling pairing module changed). See `research/MAINT/ATTEMPTS_123.md`.

Lane 082, task A04.  One bounded unit: three lemma families in one new module
`formalization/NSFormalization/Section4/A04/RealPairing.lean`, importing
`NSFormalization.Section4.A04.LaplacianPairing` (lane 076) and
`NSFormalization.Section4.D01.DerivativeDatum`.  **No datum assembly here** (that is step 3b).

## Declarations delivered (11, namespace `NSFormalization.Paper3`)

All theorems; the module has no `def`.  Current `file:line` in
`Section4/A04/RealPairing.lean`:

| # | declaration | line | role |
|---|---|---|---|
| 1 | `real_inner_eq_re_complex` | :66 | helper: `⟪x,y⟫_ℝ = re ⟪x,y⟫_ℂ` bridge |
| 2 | `realSobolev_inner_eq_ambient` | :77 | Lemma 1 subtype↔ambient inner (`rfl`) |
| 3 | `real_inner_angularDirectionalDerivative` | :84 | **Lemma 1** (ambient skew-adjointness) |
| 4 | `real_inner_angularDirectionalDerivativeReal` | :96 | Lemma 1 subtype face |
| 5 | `lowering_mid_symbol_eq` | :114 | **Lemma 3** closed form |
| 6 | `lowering_mid_symbol_order_indep` | :138 | **Lemma 3** order-independence (shift form) |
| 7 | `angularOrderLoweringMid_self` | :148 | helper: mid lowering = id at equal orders |
| 8 | `angularOrderLowering_self` | :157 | `angularOrderLowering s s _ = id` (Lemma 2 special case) |
| 9 | `inner_loweringMid_pairing` | :168 | helper: complex mid pairing |
| 10 | `inner_lowering_pairing_complex` | :199 | helper: complex full-operator pairing |
| 11 | `real_inner_lowering_pairing` | :218 | **Lemma 2** (real lowering pairing) |

(Declaration count is 11, not 10 — `angularOrderLoweringMid_self` :148 is the extra helper used by
`angularOrderLowering_self`.  Line numbers are current after the F1 docstring note was added to
`real_inner_lowering_pairing`, which shifted only its own theorem line, :214 → :218.)

## The real inner product on the carrier — exact instance path

For `x y : Lp ℂ 2 volume`, `⟪x, y⟫_ℝ = @inner ℝ _ L2.innerProductSpace x y`, where
`#synth InnerProductSpace ℝ (Lp ℂ 2 volume) = MeasureTheory.L2.innerProductSpace` (at `𝕜 = ℝ`):
`⟪x, y⟫_ℝ = ∫ ξ, ⟪x ξ, y ξ⟫_ℝ ∂volume` with the **scalar** real inner product on `ℂ`.  The scalar
instance is `#synth InnerProductSpace ℝ ℂ = instInnerProductSpaceRealComplex`.  Crucially this is
**not** `Inner.rclikeToReal ℂ` at the `Lp` level (confirmed: `#synth` returns `L2.innerProductSpace`,
and `real_inner_eq_re_inner` — stated for `rclikeToReal` — does not unify at the `Lp` level).

The step-3b consumer's carrier `RealVectorSobolev m = PiLp 2 (Fin 3) (RealSobolevHilbert m)` uses
`PiLp.innerProductSpace` over `Paper3.realSobolevInnerProductSpace s`
(`Paper3/RealPositiveDensity.lean:27`) `= Submodule.innerProductSpace` on `(realSubspace s).toSubmodule`
inside `Lp ℂ 2 volume`.  **New finding:** the subtype↔ambient inner bridge
`(inner ℝ x y : ℝ) = inner ℝ (x : FourierData) (y : FourierData)` for `x y : RealSobolevHilbert s`
is **`rfl`** (`realSobolev_inner_eq_ambient`), as is the norm bridge `‖x‖ = ‖(x : FourierData)‖`.
(This is not in tension with review finding F2: F2 is about `⟪x,y⟫_ℝ = re ⟪x,y⟫_ℂ`, a real-vs-complex
bridge, which really is not `rfl`.  The subtype bridge is real-vs-real and *is* `rfl`.)  So step 3b can
freely move its `RealSobolevHilbert`/`RealVectorSobolev` datum inner products (and norms) down to the
ambient `Lp ℂ 2 volume` carrier that all three lemmas live on.

## Route as executed

### Route A (task's recommended) — NOT AVAILABLE

Re-run 076 directly on `angularDirectionalDerivativeReal` under the real `L2.inner_def`, transporting
across `angularFrequencyDilation.restrictScalars ℝ` (a `≃ₗᵢ[ℝ]`) with `inner_map_map`.  **Blocked:**
Mathlib has **no `LinearIsometryEquiv.restrictScalars`** (nor `LinearIsometry.restrictScalars`).
`grep -rn "restrictScalars" Mathlib/Analysis/Normed/Operator/LinearIsometry.lean` is empty; a
library-wide grep for `LinearIsometryEquiv.*restrictScalars` finds nothing.  `.restrictScalars ℝ`
exists only for `ContinuousLinearMap`/`ContinuousLinearEquiv`/`LinearMap`, none of which give a
real `LinearIsometryEquiv` with `inner_map_map`.  So `U = angularFrequencyDilation` (a `≃ₗᵢ[ℂ]`)
cannot be re-used as a real isometry for the real inner product.  Not pursued further.

### Route B (task's alternative) — USED, clean

One L²-level bridge, proved once (`real_inner_eq_re_complex`):
`(inner ℝ x y : ℝ) = RCLike.re (inner ℂ x y)` on `Lp ℂ 2 volume`.  Proof (4 lines):
`MeasureTheory.L2.inner_def` at both `𝕜`; `← MeasureTheory.integral_re (L2.integrable_inner x y)`
to pull `re` outside the complex integral (integrability from `L2.integrable_inner`); then
`integral_congr_ae` + `Filter.Eventually.of_forall` reduces to the **pointwise scalar** identity
`real_inner_eq_re_inner ℂ (x ξ) (y ξ)` — which *does* apply on the scalar `ℂ` (the scalar instance
`instInnerProductSpaceRealComplex` is compatible with it; `exact?` confirmed).  So `re` moves past
`∫` exactly once, here, and never inside the theorem proofs.

Both real theorems are then real parts of lane 076's complex results:
* Lemma 1: `re ⟪f, D g⟫_ℂ = re (-⟪D f, g⟫_ℂ) = -⟪D f, g⟫_ℝ`, using `inner_angularDirectionalDerivative_right`
  (076) and `map_neg`.
* Lemma 2: transport 076-style across `U` (`angularOrderLowering_eq_dilation_mid` + `U.inner_map_map`)
  to the middle operators, prove the middle pairing by `L2.inner_def` + the symbol arithmetic below,
  then take `re` and close the norm with `inner_self_eq_norm_sq (𝕜 := ℂ)`.

### Symbol arithmetic (Lemma 3, the "not-in-tree" content)

`lowering_mid_symbol_eq`: the lowering middle symbol
`angularWeightSymbol r ξ · sobolevBesselWeight (r-s) ξ · angularWeightSymbol (-s) ξ` collapses to
`sobolevBesselWeight (r-s) (frequencyUnit • ξ)`.  Proof by `sobolevBesselWeight_mul` bookkeeping,
mirroring the in-tree `weight_product_order_indep`: the two `angularWeightSymbol` factors expand into
four `sobolevBesselWeight`s; the `frequencyUnit•ξ` pair fuses to `W_{r-s}(c•ξ)` and the `ξ` triple
`W_{-r}·W_{r-s}·W_s` fuses to `W_0 = 1`.  This closed form manifestly depends only on `r - s`; the
requested shift form `lowering_mid_symbol_order_indep` (shift both orders by `c`) is then two rewrites.
Lemma 2's `ρ_{s→r}·ρ_{s→t} = ρ_{s→(r+t)/2}²` is `sobolevBesselWeight_mul` on `c•ξ` with the exponent
identity `(r-s)+(t-s) = 2·((r+t)/2 - s)` by `ring`.

### Lemma 3 form chosen — and why not the commutation

The task offered two forms for Lemma 3: (a) the symbol order-independence, or (b) the operator
commutation `angularDirectionalDerivative (s-1) a ∘ angularOrderLowering s (s-1) _ =
angularOrderLowering (s-1) (s-2) _ ∘ angularDirectionalDerivative s a`.  **Chose (a).**  Reasons:
* (a) is the atomic analytic fact (≈3 lines, the task's own estimate) and is exactly what Lemma 2
  consumes internally.
* Step 3b's reconciliation `⟪datum_{m-1} v, datum_{m+1} v⟫ = ‖datum_m v‖²` is discharged by
  **datum uniqueness** (`D01.isSobolevDatum_unique`) to write `datum_{m-1} v = Λ_{m+1→m-1}(datum_{m+1} v)`,
  `datum_m v = Λ_{m+1→m}(datum_{m+1} v)`, and then **Lemma 2** (with `s=m+1, r=m-1, t=m+1`).  The
  commutation (b) is only the *alternative* route F1 mentions ("or, equivalently, a commutation"),
  not needed once Lemma 2 exists.
* (b) is an operator/CLM identity (compose two `U∘M∘U⁻¹`, show the middle multiplications coincide,
  `ContinuousLinearMap.ext`) — >3 lines and assembly-flavored, outside this lane's "pairing identities"
  scope.  If step 3b ever wants it: both sides reduce to `U ∘ (M₁∘M₂) ∘ U⁻¹`, and the middle equality
  is `mid_symbol_order_independent` (for the directional factor, in tree) × `lowering_mid_symbol_order_indep`
  (for the lowering factor, this lane), commuted by `mul_comm`; recipe recorded, not built.

## Failed / adjusted approaches (negative record)

* **`LinearIsometryEquiv.restrictScalars ℝ` (Route A).**  Does not exist in Mathlib (see above).
  Abandoned Route A entirely.
* **First `lowering_mid_symbol_eq` rewrite ordering.**  Applying `sobolevBesselWeight_mul (-r) (r-s)`
  left the exponent `-r + (r-s)` un-normalized, so the next factor `W_{-s}·W_s` did not match.  Fixed
  by interleaving `show -r + (r - s) = -s from by ring` **before** the `W_{-s}·W_s` rewrite.  (Recorded
  because it is the same buffer-order hazard as elsewhere in these symbol proofs.)
* **Subtype skew-adjointness with a single subtype inner product.**  Ill-typed: `f : RealSobolevHilbert s`
  but `angularDirectionalDerivativeReal s a g : RealSobolevHilbert (s-1)` — different subtypes, no shared
  inner product.  Resolved by stating the subtype form (`real_inner_angularDirectionalDerivativeReal`)
  at the shared **ambient** carrier via the `angularDirectionalDerivativeReal_coe` (`rfl`) coercions,
  exactly as the task predicted.
* **Normalizing Lemma 2's midpoint with `rw` (F1, the first thing step 3b hits).**  The midpoint
  `(r + t) / 2` is a *dependent* index of `angularOrderLowering` — the proof argument `hms` mentions
  it — so after `have h := real_inner_lowering_pairing (m+1) (m-1) (m+1) …`,
  `rw [show (m - 1 + (m + 1)) / 2 = m from by ring] at h` **fails** with `motive is not type correct`.
  Use `simp only [show (m - 1 + (m + 1)) / 2 = m from by ring] at h` instead (it has a strategy for
  proof-valued dependencies).  Recorded in the `real_inner_lowering_pairing` docstring too.  The
  reviewer's ready-made 3b reconciliation (probes `/tmp/rev082/`, elaborates as is):
  ```
  example (m : ℝ) (h1 : m - 1 ≤ m + 1) (h3 : m ≤ m + 1) (A : RealSobolevHilbert (m + 1)) :
      (inner ℝ (lowerDatum (m + 1) (m - 1) h1 A) A : ℝ) = ‖lowerDatum (m + 1) m h3 A‖ ^ 2 := by
    have h := real_inner_lowering_pairing (m + 1) (m - 1) (m + 1) h1 le_rfl (by linarith) (A : FourierData)
    rw [angularOrderLowering_self] at h
    simp only [show (m - 1 + (m + 1)) / 2 = m from by ring] at h
    exact h
  ```
  i.e. `⟪datum_{m-1} v, datum_{m+1} v⟫_ℝ = ‖datum_m v‖²` verbatim (`A03.coe_lowerDatum` and the
  subtype norm/inner bridges are all `rfl`, so `exact h` closes it with no glue).

## Brief for step 3b (the lemmas it will call)

All on the ambient carrier `Lp ℂ 2 volume`; convert to/from `RealSobolevHilbert`/`RealVectorSobolev`
with `realSobolev_inner_eq_ambient` (`rfl`) and `‖x‖ = ‖(x:FourierData)‖` (`rfl`), summed over `Fin 3`
by the `PiLp 2` inner/norm decomposition.

1. `real_inner_angularDirectionalDerivative s a f g` — `⟪f, D_a g⟫_ℝ = -⟪D_a f, g⟫_ℝ` (ambient), or its
   subtype face `real_inner_angularDirectionalDerivativeReal` on `angularDirectionalDerivativeReal`.
   Use with `g = D_a f` to get `⟪f, D_a D_a f⟫_ℝ = -‖D_a f‖²`; the `≤` weakening of
   `A04.inner_energy_assembly` (`Section4/A04/HighEnergy.lean:101`, `0 ≤ ν`) then only needs one direction.
2. `real_inner_lowering_pairing s r t hrs hts hms w` — `⟪Λ_{s→r} w, Λ_{s→t} w⟫_ℝ = ‖Λ_{s→(r+t)/2} w‖²`.
   Datum case: `s = m+1`, `r = m-1`, `t = m+1` (so `(r+t)/2 = m`); with `A = datum_{m+1} v`,
   `datum_{m-1} v = Λ_{m+1→m-1} A`, `datum_{m+1} v = Λ_{m+1→m+1} A = A` (`angularOrderLowering_self`),
   `datum_m v = Λ_{m+1→m} A`.  Supply `hms` by `by linarith` from `hrs, hts`.  **Normalize the midpoint
   with `simp only [show (r+t)/2 = m from by ring]`, not `rw` (F1 hazard above).**  The full four-line
   reconciliation is written out under "Failed / adjusted approaches".
3. `angularOrderLowering_self s hrs w = w` — collapses the `t = s` slot in the datum case.
4. `lowering_mid_symbol_order_indep` / `lowering_mid_symbol_eq` — if step 3b must identify lowering data
   across orders directly (the lowering analogue of `mid_symbol_order_independent`).
5. Datum-order identification is `D01.isSobolevDatum_unique` (`D01/ForceClass.lean:286`) +
   `A03.lowerDatum`/`A03.coe_lowerDatum` (`A03/RealAngularProduct.lean:140,144`), routed through the
   **scalar↔vector datum bridge** `A03.isSobolevDatum_iff` (`A03/VectorTameProduct.lean:54`) and the
   scalar lowering fact `A03.IsScalarSobolevDatum.lower` (`A03/ScalarTameProduct.lean:114`) — because
   `A03.lowerDatum` is a *scalar* `RealSobolevHilbert s → RealSobolevHilbert r` map while
   `isSobolevDatum_unique` is a *vector* statement about `RealVectorSobolev s`.  `D_j datum_k u =
   datum_{k-1}(∂_j u)` is `isSobolevDatum_partialDeriv` (`Section4/D01/DerivativeDatum.lean:245`).
   **Casting wrinkle:** `isSobolevDatum_partialDeriv` is `ℕ`-indexed (orders `(m:ℝ)+1 → (m:ℝ)`); to
   reach the order-`m-1` datum of `∂ⱼu` (the left slot) instantiate it at `m-1 : ℕ`, which needs
   `1 ≤ m` and a `Nat.cast_sub` step to see `((m-1:ℕ):ℝ) + 1 = (m:ℝ)`.
6. `A04.gradientSobolevENorm_toReal_sq_eq_datum_sum` (`Section4/A04/LaplacianDatum.lean:130`) — the
   **right-hand side the reconciliation must match**: it delivers `grad² = ∑ⱼ ‖D_j (datum_{m+1} u)‖²`.
7. `D01.isSobolevDatum_add` (`Section4/D01/ForceClass.lean:261`, the `RealVectorSobolev` form) — the
   second assembly input: `datum_m(Δu) = ∑ⱼ D_j (D_j (datum_{m+2} u))` needs `isSobolevDatum_partialDeriv`
   **twice** plus datum additivity over the three directions.
   (All of 5–7 are already in tree; this lane adds only 1–4.)

**Do not look for a `Λ∘Λ` composition law (F6).**  Lane 076's `inner_angularOrderLowering`
(self-adjointness of the full lowering) is **not used** by this route: Lemma 2 is re-derived directly
from `angularOrderLoweringMid_coeFn` + the symbol algebra, because deriving the pairing from
self-adjointness would need a composition law `Λ_{s→r} ∘ Λ_{s→t} = Λ_{s→mid} ∘ Λ_{s→mid}` that is
**not in tree**.  076's step-2 deliverable is therefore unused by SL3; step 3b should not search for it.

## Commands run

- `cd verification && lake build NSFormalization.Section4.A04.RealPairing` →
  `Built NSFormalization.Section4.A04.RealPairing (3.5s)` / `Build completed successfully (9893 jobs).`
  (only pre-existing replayed upstream warnings: `SchwartzMap.smul_apply`, `if_pos`, an unused simp arg).
- `cd verification && lake env lean ../formalization/NSFormalization/Section4/A04/RealPairing.lean` →
  empty output, exit 0 (zero warnings, default heartbeat budget, no `set_option`).
- `cd verification && lake env lean ../research/A04/axioms_sl3_real.lean` → all **11** public
  declarations depend only on `[propext, Classical.choice, Quot.sound]`.
- `grep -nE 'sorry|admit|axiom|native_decide|maxHeartbeats' …/RealPairing.lean` → no match.
- `make check` (worktree root) → exit 0.
