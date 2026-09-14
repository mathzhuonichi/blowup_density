import NSFormalization.Section4.A04.RealPairing

/-!
# A04 unit G1, sub-lemma SL5 — the nonlinear pairing (S items)

`research/A04/SL5_SPLIT.md`.  SL5 is the `hnl` input of `A04.inner_energy_assembly` /
`inner_energy_Rhigh` (`HighEnergy.lean:100,136`):

`− ⟪G t, N⟫_ℝ ≤ gradientSobolevNormAt (m:ℝ) u t · (outerSobolevENorm (m:ℝ) (u t·) (u t·)).toReal`,

with `G t` the order-`m` datum of `u(t,·)` and `N` the order-`m` datum of the advection
slice `advection u t = (u·∇)u(t,·)` (`MomentumDatum.lean:167-179`).  The full unit is rated
**L**; this module supplies its **S** ingredients.

* **SL5(e)** — the discrete Cauchy–Schwarz bound for a finite sum of inner products,
  `∑ⱼ ⟪aⱼ, bⱼ⟫ ≤ √(∑ⱼ ‖aⱼ‖²)·√(∑ⱼ ‖bⱼ‖²)` (and its `|·|` companion), on **any** real inner
  product space.  This is the bound applied to the columns after the integration by parts,
  with `aⱼ = Dⱼ(datum_{m+1} u)` and `bⱼ = datum_m Wⱼ`.
* **SL5(d)** — the summed real skew-adjointness of the angular directional-derivative operator,
  a corollary of lane 082 (`A04.RealPairing`).  Provided on the ambient `Lp ℂ 2 volume` carrier
  (`sum_real_inner_angularDirectionalDerivative`, the form the double-sum IBP consumes, since
  `G i` and `datum Wⱼ` live at different orders on the shared ambient space) and on the
  datum-carrier subtype at a common order (`sum_real_inner_angularDirectionalDerivativeReal`).
* **SL5(i)** — the **two-vector, two-source-order lowering transfer**
  `⟪Λ_{s→r} v, Λ_{s'→t} w⟫ = ⟪Λ_{s→r'} v, Λ_{s'→t'} w⟫` whenever `r + t = r' + t'`, in the mid /
  complex / real layers mirroring `RealPairing.lean:168/199/218`.  This is SL5's only genuinely
  new analytic content: 082's `real_inner_lowering_pairing` is single-vector (both slots descend
  from the same datum), while SL5's IBP has `u` in one slot and `Wⱼ = uⱼ·u` in the other, so the
  two source orders must be freed.  It reconciles the forced order `m+1` on the column side with
  the target `‖u⊗u‖_{H^m}` without the crude `‖Λ_{m→m-1}(Dⱼ A')‖ ≤ ‖Dⱼ A'‖` bound (which would
  leave the weaker `‖u⊗u‖_{H^{m+1}}` on the right).

The remaining SL5 rows (5a pointwise divergence form, 5b/5c the column data, 5f/5g the norm
identifications, 5h the calc assembly) are catalogued in `SL5_SPLIT.md`; lane 088's
`A04/LaplacianAssembly.lean` (PR #94, merged to `erenup/integration` after this worktree branched)
closed SL3 and supplies the order-transport machinery 5c/5h reuse.
-/

noncomputable section

open MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Source.RealSobolev (RealSobolevHilbert FourierData)
open NSFormalization.Source (frequencyUnit)
open scoped InnerProductSpace ComplexConjugate

namespace NSFormalization.Paper3

/-! ## 0. SL5(i): the two-vector, two-source-order lowering transfer

Generalizes lane 082's single-vector `inner_loweringMid_pairing` / `inner_lowering_pairing_complex`
/ `real_inner_lowering_pairing` (`RealPairing.lean:168/199/218`) to **two** vectors and **two**
independent source orders.  The pairing depends on the orders only through the *sum* of the two
lowering amounts, because each lowering middle symbol collapses (via `lowering_mid_symbol_eq`) to
`sobolevBesselWeight (·) (frequencyUnit • ξ)` and `sobolevBesselWeight` is multiplicative. -/

/-- **SL5(i), mid layer.**  The complex pairing of two lowering *middle* operators applied to
different vectors `v`, `w` at different source orders `s`, `s'` depends on the four orders only
through `r + t`: `⟪Λ_{s→r} v, Λ_{s'→t} w⟫ = ⟪Λ_{s→r'} v, Λ_{s'→t'} w⟫` whenever `r + t = r' + t'`.
The two `ring` steps of 082's `inner_loweringMid_pairing` never used `v = w`; here the shared
factor is `conj (v ξ) · w ξ` and the symbol product `b_{r-s}·b_{t-s'} = b_{r'-s}·b_{t'-s'}`
(`sobolevBesselWeight_mul`, exponents equal under `r + t = r' + t'`). -/
theorem inner_loweringMid_transfer (s s' r t r' t' : ℝ) (h : r + t = r' + t')
    (hrs : r ≤ s) (hts : t ≤ s') (hrs' : r' ≤ s) (hts' : t' ≤ s')
    (v w : Lp ℂ 2 (volume : Measure Space)) :
    ⟪angularOrderLoweringMid s r hrs v, angularOrderLoweringMid s' t hts w⟫_ℂ =
      ⟪angularOrderLoweringMid s r' hrs' v, angularOrderLoweringMid s' t' hts' w⟫_ℂ := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [angularOrderLoweringMid_coeFn s r hrs v,
    angularOrderLoweringMid_coeFn s' t hts w,
    angularOrderLoweringMid_coeFn s r' hrs' v,
    angularOrderLoweringMid_coeFn s' t' hts' w] with ξ hr ht hr' ht'
  have conjW : ∀ a : ℝ, conj (sobolevBesselWeight a (frequencyUnit • ξ)) =
      sobolevBesselWeight a (frequencyUnit • ξ) := by
    intro a; simp [sobolevBesselWeight]
  have hsym : sobolevBesselWeight (r - s) (frequencyUnit • ξ) *
        sobolevBesselWeight (t - s') (frequencyUnit • ξ) =
      sobolevBesselWeight (r' - s) (frequencyUnit • ξ) *
        sobolevBesselWeight (t' - s') (frequencyUnit • ξ) := by
    have h1 := congrFun (sobolevBesselWeight_mul (r - s) (t - s')) (frequencyUnit • ξ)
    have h2 := congrFun (sobolevBesselWeight_mul (r' - s) (t' - s')) (frequencyUnit • ξ)
    simp only [Pi.mul_apply] at h1 h2
    rw [h1, h2, show r - s + (t - s') = r' - s + (t' - s') from by linarith]
  simp only [RCLike.inner_apply, hr, ht, hr', ht', lowering_mid_symbol_eq]
  rw [map_mul, conjW, map_mul, conjW]
  linear_combination (conj (v ξ) * w ξ) * hsym

/-- **SL5(i), complex layer.**  The same transfer for the full `angularOrderLowering` operators,
by transporting the mid layer across the unitary `U = angularFrequencyDilation`
(`angularOrderLowering_eq_dilation_mid` + `LinearIsometryEquiv.inner_map_map`), exactly as
082's `inner_lowering_pairing_complex`. -/
theorem inner_lowering_transfer_complex (s s' r t r' t' : ℝ) (h : r + t = r' + t')
    (hrs : r ≤ s) (hts : t ≤ s') (hrs' : r' ≤ s) (hts' : t' ≤ s')
    (v w : Lp ℂ 2 (volume : Measure Space)) :
    ⟪angularOrderLowering s r hrs v, angularOrderLowering s' t hts w⟫_ℂ =
      ⟪angularOrderLowering s r' hrs' v, angularOrderLowering s' t' hts' w⟫_ℂ := by
  rw [angularOrderLowering_eq_dilation_mid s r, angularOrderLowering_eq_dilation_mid s' t,
    angularOrderLowering_eq_dilation_mid s r', angularOrderLowering_eq_dilation_mid s' t',
    angularFrequencyDilation.inner_map_map, angularFrequencyDilation.inner_map_map]
  exact inner_loweringMid_transfer s s' r t r' t' h hrs hts hrs' hts'
    (angularFrequencyDilation.symm v) (angularFrequencyDilation.symm w)

/-- **SL5(i), real layer.**  The real-carrier transfer
`⟪Λ_{s→r} v, Λ_{s'→t} w⟫_ℝ = ⟪Λ_{s→r'} v, Λ_{s'→t'} w⟫_ℝ` for `r + t = r' + t'`, the real part of
`inner_lowering_transfer_complex` via `real_inner_eq_re_complex`.  This is the form SL5's assembly
consumes to move the forced column order `m+1` onto the shared order `m`: with `s = m`, `s' = m+1`
it turns `⟪Λ_{m→m-1}(Dⱼ A'), Λ_{m+1→m+1}(Bⱼ)⟫` into `⟪Λ_{m→m}(Dⱼ A'), Λ_{m+1→m}(Bⱼ)⟫`. -/
theorem real_inner_lowering_transfer (s s' r t r' t' : ℝ) (h : r + t = r' + t')
    (hrs : r ≤ s) (hts : t ≤ s') (hrs' : r' ≤ s) (hts' : t' ≤ s')
    (v w : Lp ℂ 2 (volume : Measure Space)) :
    (inner ℝ (angularOrderLowering s r hrs v) (angularOrderLowering s' t hts w) : ℝ) =
      (inner ℝ (angularOrderLowering s r' hrs' v) (angularOrderLowering s' t' hts' w) : ℝ) := by
  rw [real_inner_eq_re_complex, real_inner_eq_re_complex,
    inner_lowering_transfer_complex s s' r t r' t' h hrs hts hrs' hts']

end NSFormalization.Paper3

namespace NSFormalization.Section4.A04

open NSFormalization.Paper3
  (RealVectorSobolev angularDirectionalDerivative angularDirectionalDerivativeReal
   real_inner_angularDirectionalDerivative real_inner_angularDirectionalDerivativeReal)

/-! ## 1. SL5(e): discrete Cauchy–Schwarz for a finite sum of inner products -/

/-- **SL5(e).**  On any real inner product space, the sum of the pairwise inner products of two
finite families is bounded by the product of the ℓ² norms of the families:
`∑ⱼ ⟪aⱼ, bⱼ⟫ ≤ √(∑ⱼ ‖aⱼ‖²)·√(∑ⱼ ‖bⱼ‖²)`.  Termwise `real_inner_le_norm`, then the real
discrete Cauchy–Schwarz `Real.sum_mul_le_sqrt_mul_sqrt`. -/
theorem sum_inner_le_sqrt_mul_sqrt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} (s : Finset ι) (a b : ι → E) :
    ∑ j ∈ s, (inner ℝ (a j) (b j) : ℝ)
      ≤ Real.sqrt (∑ j ∈ s, ‖a j‖ ^ 2) * Real.sqrt (∑ j ∈ s, ‖b j‖ ^ 2) := by
  calc ∑ j ∈ s, (inner ℝ (a j) (b j) : ℝ)
      ≤ ∑ j ∈ s, ‖a j‖ * ‖b j‖ :=
        Finset.sum_le_sum (fun j _ => real_inner_le_norm (a j) (b j))
    _ ≤ Real.sqrt (∑ j ∈ s, ‖a j‖ ^ 2) * Real.sqrt (∑ j ∈ s, ‖b j‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt s (fun j => ‖a j‖) (fun j => ‖b j‖)

/-- **SL5(e), absolute-value form.**  The same bound for the absolute value of the sum, so the
sign of `∑ⱼ ⟪aⱼ, bⱼ⟫` need not be tracked when the IBP produces `-⟪G, N⟫`.  Termwise
`abs_real_inner_le_norm` after the triangle inequality `Finset.abs_sum_le_sum_abs`. -/
theorem abs_sum_inner_le_sqrt_mul_sqrt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} (s : Finset ι) (a b : ι → E) :
    |∑ j ∈ s, (inner ℝ (a j) (b j) : ℝ)|
      ≤ Real.sqrt (∑ j ∈ s, ‖a j‖ ^ 2) * Real.sqrt (∑ j ∈ s, ‖b j‖ ^ 2) := by
  calc |∑ j ∈ s, (inner ℝ (a j) (b j) : ℝ)|
      ≤ ∑ j ∈ s, |(inner ℝ (a j) (b j) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ s, ‖a j‖ * ‖b j‖ :=
        Finset.sum_le_sum (fun j _ => abs_real_inner_le_norm (a j) (b j))
    _ ≤ Real.sqrt (∑ j ∈ s, ‖a j‖ ^ 2) * Real.sqrt (∑ j ∈ s, ‖b j‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt s (fun j => ‖a j‖) (fun j => ‖b j‖)

/-! ## 2. SL5(d): summed real skew-adjointness of the directional-derivative operator -/

/-- **SL5(d), ambient carrier.**  Real skew-adjointness of `angularDirectionalDerivative s a`,
summed over the three Euclidean components on the ambient `Lp ℂ 2 volume` carrier:
`∑ᵢ ⟪fᵢ, D gᵢ⟫_ℝ = -∑ᵢ ⟪D fᵢ, gᵢ⟫_ℝ`.  A finset-sum of lane 082's
`real_inner_angularDirectionalDerivative`.  This is the form the double-sum integration by
parts of SL5 consumes: after `N = ∑ⱼ datum(∂ⱼWⱼ)` the pairing `⟪G, datum(∂ⱼWⱼ)⟫` expands
componentwise into ambient inner products with `G i` (order `m`) and the column datum
`B_j i` (order `m+1`) sitting on the shared `FourierData`, at different subtype orders. -/
theorem sum_real_inner_angularDirectionalDerivative (s : ℝ) (a : Space)
    (f g : Fin 3 → FourierData) :
    ∑ i : Fin 3, (inner ℝ (f i) (angularDirectionalDerivative s a (g i)) : ℝ)
      = -∑ i : Fin 3, (inner ℝ (angularDirectionalDerivative s a (f i)) (g i) : ℝ) := by
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl
    (fun i _ => real_inner_angularDirectionalDerivative s a (f i) (g i))

/-- **SL5(d), datum-carrier subtype.**  The vector lift of lane 082's
`real_inner_angularDirectionalDerivativeReal` to `RealVectorSobolev s`: summed over the three
components, `∑ᵢ ⟪fᵢ, D gᵢ⟫_ℝ = -∑ᵢ ⟪D fᵢ, gᵢ⟫_ℝ`, with `f g` at the common order `s` and the
pairing read on the shared ambient carrier via the coercions (`angularDirectionalDerivativeReal`
lowers `s` to `s - 1`, so the two arguments live in different subtypes). -/
theorem sum_real_inner_angularDirectionalDerivativeReal (s : ℝ) (a : Space)
    (f g : RealVectorSobolev s) :
    ∑ i : Fin 3, (inner ℝ ((f i : FourierData))
        ((angularDirectionalDerivativeReal s a (g i) : RealSobolevHilbert (s - 1))
          : FourierData) : ℝ)
      = -∑ i : Fin 3, (inner ℝ
          ((angularDirectionalDerivativeReal s a (f i) : RealSobolevHilbert (s - 1)) : FourierData)
          ((g i : FourierData)) : ℝ) := by
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl
    (fun i _ => real_inner_angularDirectionalDerivativeReal s a (f i) (g i))

end NSFormalization.Section4.A04
