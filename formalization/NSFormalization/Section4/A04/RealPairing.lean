import NSFormalization.Section4.A04.LaplacianPairing
import NSFormalization.Section4.D01.DerivativeDatum

/-!
# A04 unit G1, sub-lemma SL3, step 3a: the real-carrier pairing identities

Lane 082.  Step 3b of the SL3 route (the Laplacian datum assembly, task A04) consumes its inner
products on the **real** inner product of `RealVectorSobolev m`, whose instance path is
`PiLp.innerProductSpace` over `Paper3.realSobolevInnerProductSpace s`
(`Paper3/RealPositiveDensity.lean:27`) `= Submodule.innerProductSpace` on
`(realSubspace s).toSubmodule` inside `Lp ℂ 2 volume` with `MeasureTheory.L2.innerProductSpace`
at `𝕜 = ℝ` — **not** `Inner.rclikeToReal ℂ`.  Lane 076
(`Section4/A04/LaplacianPairing.lean`) proved the adjointness/self-adjointness facts on the
**complex** `L²` inner product only; this module supplies their real-carrier counterparts, plus
the datum-order reconciliation and the lowering-symbol order-independence step 3b needs.

Three lemma families, all stated on the ambient carrier `Lp ℂ 2 volume` for the real inner
product (`𝕜 = ℝ`), with the subtype form recorded where step 3b uses it:

* **Lemma 1 — real skew-adjointness** (`real_inner_angularDirectionalDerivative`,
  `real_inner_angularDirectionalDerivativeReal`).  `⟪f, D_a g⟫_ℝ = -⟪D_a f, g⟫_ℝ`.
* **Lemma 2 — the lowering pairing** (`real_inner_lowering_pairing`).
  `⟪Λ_{s→r} w, Λ_{s→t} w⟫_ℝ = ‖Λ_{s→(r+t)/2} w‖²`, the `⟪Λ⁻¹w, Λw⟫ = ‖w‖²` reconciliation.
* **Lemma 3 — lowering-symbol order-independence** (`lowering_mid_symbol_eq`,
  `lowering_mid_symbol_order_indep`).  The lowering middle symbol equals
  `sobolevBesselWeight (r - s) (frequencyUnit • ξ)`, hence depends only on `r - s`.

## Route (recorded)

The task's recommended route (re-run 076 directly on `angularDirectionalDerivativeReal` under the
real `L2.inner_def`, transporting across `angularFrequencyDilation.restrictScalars ℝ`) is **not
available**: Mathlib has no `LinearIsometryEquiv.restrictScalars` (grep over
`Mathlib/Analysis/Normed/Operator/LinearIsometry.lean` and the whole library finds none), so the
unitary `U = angularFrequencyDilation` (a `≃ₗᵢ[ℂ]`) cannot be turned into a `≃ₗᵢ[ℝ]` to reuse
`inner_map_map` for the real inner product.

The **alternative** route works cleanly and is used here: the L²-level bridge
`⟪x, y⟫_ℝ = re ⟪x, y⟫_ℂ` on `Lp ℂ 2 volume` (`real_inner_eq_re_complex`), proved once from
`MeasureTheory.L2.inner_def` (both `𝕜`), `MeasureTheory.integral_re` (integrability from
`MeasureTheory.L2.integrable_inner`) and the *scalar* identity `real_inner_eq_re_inner ℂ` (which
**does** apply pointwise on `ℂ`, since the scalar `InnerProductSpace ℝ ℂ` is
`instInnerProductSpaceRealComplex`).  Both real theorems then follow from 076's complex results by
taking real parts; the `re` never has to move past `∫` in the theorem proofs themselves, only in
this one bridge.  The generic subtype↔ambient inner bridge `realSobolev_inner_eq_ambient` is
`rfl` (the `Submodule` inner product is the ambient one on coercions), so step 3b can convert the
`RealSobolevHilbert` inner products of its datum to the ambient inner products these lemmas use.
-/

noncomputable section

open MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Source.RealSobolev (RealSobolevHilbert FourierData)
open NSFormalization.Source (frequencyUnit)
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace NSFormalization.Paper3

/-! ## 0. The real inner product on the `L²` carrier -/

/-- **The real↔complex inner-product bridge on `Lp ℂ 2 volume`.**  The real inner product
(`MeasureTheory.L2.innerProductSpace` at `𝕜 = ℝ`, `∫ ⟪x ξ, y ξ⟫_ℝ`) is the real part of the
complex one.  Proved from `L2.inner_def` at both fields, `integral_re` (integrand integrable by
`L2.integrable_inner`) and the pointwise scalar fact `real_inner_eq_re_inner ℂ`; it is **not**
`rfl` and Mathlib's `real_inner_eq_re_inner` does not apply at the `Lp` level (that lemma is for
`Inner.rclikeToReal`, which is not this instance). -/
theorem real_inner_eq_re_complex (x y : Lp ℂ 2 (volume : Measure Space)) :
    (inner ℝ x y : ℝ) = RCLike.re (inner ℂ x y) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def,
    ← integral_re (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) x y)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun ξ => ?_))
  exact real_inner_eq_re_inner ℂ (x ξ) (y ξ)

/-- **Subtype↔ambient inner bridge.**  The real inner product of `RealSobolevHilbert s` is the
ambient `Lp ℂ 2 volume` real inner product on the coercions (`Submodule.innerProductSpace`), by
`rfl`.  This lets step 3b move its `RealSobolevHilbert`-valued datum inner products to the ambient
carrier the pairing identities live on. -/
theorem realSobolev_inner_eq_ambient (s : ℝ) (x y : RealSobolevHilbert s) :
    (inner ℝ x y : ℝ) = (inner ℝ (x : FourierData) (y : FourierData) : ℝ) := rfl

/-! ## 1. Real skew-adjointness of the angular directional derivative (Lemma 1) -/

/-- **Real skew-adjointness** on the ambient carrier: `⟪f, D_a g⟫_ℝ = -⟪D_a f, g⟫_ℝ`.  The real
part of lane 076's complex `inner_angularDirectionalDerivative_right`. -/
theorem real_inner_angularDirectionalDerivative (s : ℝ) (a : Space)
    (f g : Lp ℂ 2 (volume : Measure Space)) :
    (inner ℝ f (angularDirectionalDerivative s a g) : ℝ) =
      -(inner ℝ (angularDirectionalDerivative s a f) g : ℝ) := by
  rw [real_inner_eq_re_complex f (angularDirectionalDerivative s a g),
    inner_angularDirectionalDerivative_right, map_neg,
    real_inner_eq_re_complex (angularDirectionalDerivative s a f) g]

/-- **Subtype form of Lemma 1**, for step 3b.  `angularDirectionalDerivativeReal s a` maps order
`s` to `s - 1`, so `f` and `D_a g` live in different subtypes; the skew-adjoint pairing is stated
at the shared ambient carrier via the coercions (`angularDirectionalDerivativeReal_coe`, `rfl`).
Combine with `realSobolev_inner_eq_ambient` to read it back inside a common-order subtype. -/
theorem real_inner_angularDirectionalDerivativeReal (s : ℝ) (a : Space)
    (f g : RealSobolevHilbert s) :
    (inner ℝ (f : FourierData)
        ((angularDirectionalDerivativeReal s a g : RealSobolevHilbert (s - 1)) : FourierData) : ℝ) =
      -(inner ℝ
          ((angularDirectionalDerivativeReal s a f : RealSobolevHilbert (s - 1)) : FourierData)
          (g : FourierData) : ℝ) := by
  rw [angularDirectionalDerivativeReal_coe, angularDirectionalDerivativeReal_coe]
  exact real_inner_angularDirectionalDerivative s a _ _

/-! ## 2. Order-independence of the lowering middle symbol (Lemma 3) -/

/-- **Closed form of the lowering middle symbol.**  The three-way product
`angularWeightSymbol r · sobolevBesselWeight (r-s) · angularWeightSymbol (-s)` collapses to the
single Bessel factor `sobolevBesselWeight (r - s) (frequencyUnit • ξ)` — the two `angularWeightSymbol`
factors and the ambient Bessel factor cancel, leaving only the dilated one, which depends on
`r` and `s` **only through `r - s`**.  This is the analytic content behind the order bookkeeping
of step 3b; it also drives the lowering pairing (Lemma 2). -/
theorem lowering_mid_symbol_eq (s r : ℝ) (ξ : Space) :
    angularWeightSymbol r ξ * sobolevBesselWeight (r - s) ξ * angularWeightSymbol (-s) ξ =
      sobolevBesselWeight (r - s) (frequencyUnit • ξ) := by
  have hc := congrFun (sobolevBesselWeight_mul r (-s)) (frequencyUnit • ξ)
  have h1 := congrFun (sobolevBesselWeight_mul (-r) (r - s)) ξ
  have h2 := congrFun (sobolevBesselWeight_mul (-s) s) ξ
  simp only [Pi.mul_apply] at hc h1 h2
  unfold angularWeightSymbol
  simp only [neg_neg]
  rw [show sobolevBesselWeight r (frequencyUnit • ξ) * sobolevBesselWeight (-r) ξ *
        sobolevBesselWeight (r - s) ξ *
        (sobolevBesselWeight (-s) (frequencyUnit • ξ) * sobolevBesselWeight s ξ) =
      (sobolevBesselWeight r (frequencyUnit • ξ) * sobolevBesselWeight (-s) (frequencyUnit • ξ)) *
        ((sobolevBesselWeight (-r) ξ * sobolevBesselWeight (r - s) ξ) * sobolevBesselWeight s ξ)
        from by ring,
    hc, h1, show -r + (r - s) = -s from by ring, h2,
    show -s + s = (0 : ℝ) from by ring, show r + -s = r - s from by ring]
  simp [sobolevBesselWeight]

/-- **Order-independence of the lowering middle symbol.**  Shifting both orders by the same `c`
leaves the middle symbol unchanged (both sides equal `sobolevBesselWeight (r - s) (frequencyUnit • ξ)`
by `lowering_mid_symbol_eq`), i.e. it depends only on `r - s`.  This is the "not-in-tree"
order-independence step 3b needs to identify lowering data across orders (the lowering analogue of
`mid_symbol_order_independent`). -/
theorem lowering_mid_symbol_order_indep (s r c : ℝ) (ξ : Space) :
    angularWeightSymbol r ξ * sobolevBesselWeight (r - s) ξ * angularWeightSymbol (-s) ξ =
      angularWeightSymbol (r + c) ξ * sobolevBesselWeight (r - s) ξ *
        angularWeightSymbol (-(s + c)) ξ := by
  rw [lowering_mid_symbol_eq, show r - s = (r + c) - (s + c) from by ring, lowering_mid_symbol_eq]

/-! ## 3. The lowering is the identity at equal orders (used by Lemma 2's special case) -/

/-- The lowering middle operator at equal orders is the identity (its symbol
`sobolevBesselWeight 0 (frequencyUnit • ξ) = 1`). -/
theorem angularOrderLoweringMid_self (s : ℝ) (hrs : s ≤ s)
    (k : Lp ℂ 2 (volume : Measure Space)) : angularOrderLoweringMid s s hrs k = k := by
  apply Lp.ext
  filter_upwards [angularOrderLoweringMid_coeFn s s hrs k] with ξ hk
  rw [hk, lowering_mid_symbol_eq]
  simp [sobolevBesselWeight]

/-- `angularOrderLowering s s _` is the identity: `U ∘ id ∘ U⁻¹`.  (The special case step 3b
consumes takes `t = s`, so the second slot of the pairing is the datum itself.) -/
theorem angularOrderLowering_self (s : ℝ) (hrs : s ≤ s)
    (w : Lp ℂ 2 (volume : Measure Space)) : angularOrderLowering s s hrs w = w := by
  rw [angularOrderLowering_eq_dilation_mid, angularOrderLoweringMid_self,
    LinearIsometryEquiv.apply_symm_apply]

/-! ## 4. The lowering pairing (Lemma 2) -/

/-- The complex pairing of the lowering **middle** operators: multiplying by the real symbols
`ρ_{s→r}` and `ρ_{s→t}` pairs, via `L2.inner_def`, to multiplying by `ρ_{s→(r+t)/2}²` — because
`ρ_{s→r} · ρ_{s→t} = sobolevBesselWeight ((r-s)+(t-s)) (c•ξ) = ρ_{s→(r+t)/2}²`
(`lowering_mid_symbol_eq` + `sobolevBesselWeight_mul`). -/
theorem inner_loweringMid_pairing (s r t : ℝ) (hrs : r ≤ s) (hts : t ≤ s)
    (hms : (r + t) / 2 ≤ s) (v : Lp ℂ 2 (volume : Measure Space)) :
    ⟪angularOrderLoweringMid s r hrs v, angularOrderLoweringMid s t hts v⟫_ℂ =
      ⟪angularOrderLoweringMid s ((r + t) / 2) hms v,
        angularOrderLoweringMid s ((r + t) / 2) hms v⟫_ℂ := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [angularOrderLoweringMid_coeFn s r hrs v, angularOrderLoweringMid_coeFn s t hts v,
    angularOrderLoweringMid_coeFn s ((r + t) / 2) hms v] with ξ hr ht hm
  simp only [RCLike.inner_apply, hr, ht, hm, lowering_mid_symbol_eq]
  have conjW : ∀ a : ℝ, conj (sobolevBesselWeight a (frequencyUnit • ξ)) =
      sobolevBesselWeight a (frequencyUnit • ξ) := by
    intro a; simp [sobolevBesselWeight]
  have hprod := congrFun (sobolevBesselWeight_mul (t - s) (r - s)) (frequencyUnit • ξ)
  have hprod2 := congrFun (sobolevBesselWeight_mul ((r + t) / 2 - s) ((r + t) / 2 - s))
    (frequencyUnit • ξ)
  simp only [Pi.mul_apply] at hprod hprod2
  rw [map_mul, conjW, map_mul, conjW,
    show sobolevBesselWeight (t - s) (frequencyUnit • ξ) * v ξ *
        (sobolevBesselWeight (r - s) (frequencyUnit • ξ) * conj (v ξ)) =
      (sobolevBesselWeight (t - s) (frequencyUnit • ξ) *
        sobolevBesselWeight (r - s) (frequencyUnit • ξ)) * (v ξ * conj (v ξ)) from by ring,
    show sobolevBesselWeight ((r + t) / 2 - s) (frequencyUnit • ξ) * v ξ *
        (sobolevBesselWeight ((r + t) / 2 - s) (frequencyUnit • ξ) * conj (v ξ)) =
      (sobolevBesselWeight ((r + t) / 2 - s) (frequencyUnit • ξ) *
        sobolevBesselWeight ((r + t) / 2 - s) (frequencyUnit • ξ)) * (v ξ * conj (v ξ)) from by ring,
    hprod, hprod2, show t - s + (r - s) = (r + t) / 2 - s + ((r + t) / 2 - s) from by ring]

/-- The complex lowering pairing on the full operators: transport `inner_loweringMid_pairing`
across the unitary `U = angularFrequencyDilation` via `LinearIsometryEquiv.inner_map_map`
(`angularOrderLowering s r hrs = U ∘ L_{s→r} ∘ U⁻¹`, `angularOrderLowering_eq_dilation_mid`). -/
theorem inner_lowering_pairing_complex (s r t : ℝ) (hrs : r ≤ s) (hts : t ≤ s)
    (hms : (r + t) / 2 ≤ s) (w : Lp ℂ 2 (volume : Measure Space)) :
    ⟪angularOrderLowering s r hrs w, angularOrderLowering s t hts w⟫_ℂ =
      ⟪angularOrderLowering s ((r + t) / 2) hms w,
        angularOrderLowering s ((r + t) / 2) hms w⟫_ℂ := by
  rw [angularOrderLowering_eq_dilation_mid s r, angularOrderLowering_eq_dilation_mid s t,
    angularOrderLowering_eq_dilation_mid s ((r + t) / 2),
    angularFrequencyDilation.inner_map_map, angularFrequencyDilation.inner_map_map]
  exact inner_loweringMid_pairing s r t hrs hts hms _

/-- **The real lowering pairing (Lemma 2).**  `⟪Λ_{s→r} w, Λ_{s→t} w⟫_ℝ = ‖Λ_{s→(r+t)/2} w‖²`,
the real-carrier `⟪Λ⁻¹w, Λw⟫ = ‖w‖²` reconciliation step 3b needs to match the differing datum
orders against the `(r+t)/2` gradient norm.  Real part of `inner_lowering_pairing_complex`, closed
with `inner_self_eq_norm_sq`.  The datum case `r = s-2`, `t = s`, midpoint `s-1`: with `t = s` the
second slot is `angularOrderLowering s s _ w = w` (`angularOrderLowering_self`).
**Usage note:** the midpoint `(r + t) / 2` is a *dependent* index of `angularOrderLowering` (the
proof `hms` mentions it), so after instantiating, normalize it with
`simp only [show (r + t) / 2 = m from by ring]`, **not** `rw` — `rw` fails with "motive is not
type correct". -/
theorem real_inner_lowering_pairing (s r t : ℝ) (hrs : r ≤ s) (hts : t ≤ s)
    (hms : (r + t) / 2 ≤ s) (w : Lp ℂ 2 (volume : Measure Space)) :
    (inner ℝ (angularOrderLowering s r hrs w) (angularOrderLowering s t hts w) : ℝ) =
      ‖angularOrderLowering s ((r + t) / 2) hms w‖ ^ 2 := by
  rw [real_inner_eq_re_complex, inner_lowering_pairing_complex s r t hrs hts hms,
    inner_self_eq_norm_sq (𝕜 := ℂ)]

end NSFormalization.Paper3
