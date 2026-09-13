import NSFormalization.Section4.A04.LaplacianDatum

/-!
# A04 unit G1, sub-lemma SL3, step 1: skew-adjointness of the directional-derivative operator

`research/A04/ATTEMPTS_SL3.md` §"What remains" step 1 (also the module docstring at the end of
`Section4/A04/LaplacianDatum.lean`).  The dissipation identity `⟪G, datum Δu⟫_{H^m} = -‖∇u‖²`
reduces, componentwise, to the scalar integration by parts `⟪a, ∂ⱼ b⟫ = -⟪∂ⱼ a, b⟫` on the
angular `L²` Fourier carrier.

The angular directional derivative factors as `angularDirectionalDerivative s a = U ∘ M_s ∘ U⁻¹`
with `U = Paper3.angularFrequencyDilation` a `LinearIsometryEquiv` (unitary) and
`M_s = W_{s-1} ∘ σ_a ∘ W_{-s}` the middle multiplication operator
`angularWeightEquiv (s-1) ∘ sobolevDirectionalDerivative s a ∘ (angularWeightEquiv s).symm`.
Since `cyclesToAngular s = (angularWeightEquiv s).trans angularFrequencyDilation`, this factoring
holds definitionally (`angularDirectionalDerivative_eq_dilation_mid`).

* `angularDirectionalMid` — the middle operator `M_s`; its a.e. coefficient function is the
  three-way symbol product of `angularWeightMap_coeFn (s-1)`,
  `sobolevDirectionalDerivative_coeFn s a` and `angularWeightMap_coeFn (-s)`
  (`angularDirectionalMid_coeFn`).
* `inner_angularDirectionalMid` — skew-adjointness of `M_s` on `L²`, from
  `MeasureTheory.L2.inner_def` + `integral_congr_ae` + `Paper3.mid_symbol_imaginary`
  (`conj σ = -σ` for the directional middle symbol).
* `inner_angularDirectionalDerivative_right` — the deliverable: transport of skew-adjointness
  across the unitary `U` via `LinearIsometryEquiv.inner_map_map` (no dilation coefficient
  function is needed).

The companion `inner_angularOrderLowering` proves the analogous *self*-adjointness of
`Paper3.angularOrderLowering` (real middle symbol, `Paper3.lowering_symbol_real`,
`conj σ = σ`) by exactly the same technique.  This is not a bonus: step 3 of the route needs the
lowering pairing `⟪Λ⁻¹w, Λw⟫ = ‖w‖²` to reconcile the differing datum orders `m`/`m+2` against
the `m+1` of the gradient norm, so `inner_angularOrderLowering` is a *required* input there (see
`research/A04/ATTEMPTS_SL3_PAIRING.md` §"What still remains").

This module supplies steps 1 and 2 of the route.  Step 3 — the Laplacian datum assembly
`datum_m(Δu) = ∑ⱼ D_j (D_j (datum_{m+2} u))` together with the datum-order reconciliation — still
remains, per the `LaplacianDatum.lean` docstring and `ATTEMPTS_SL3_PAIRING.md`.
-/

noncomputable section

open MeasureTheory NavierStokes.ProblemStatement
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace NSFormalization.Paper3

/-! ## 1. The directional middle multiplication operator `M_s = W_{s-1} ∘ σ_a ∘ W_{-s}` -/

/-- The middle multiplication operator obtained by stripping the unitary dilation `U` off
`angularDirectionalDerivative`: `M_s = angularWeightEquiv (s-1) ∘ sobolevDirectionalDerivative s a
∘ (angularWeightEquiv s).symm`. -/
def angularDirectionalMid (s : ℝ) (a : Space) :
    Lp ℂ 2 (volume : Measure Space) →L[ℂ] Lp ℂ 2 (volume : Measure Space) :=
  (angularWeightEquiv (s - 1)).toContinuousLinearMap.comp
    ((sobolevDirectionalDerivative s a).comp (angularWeightEquiv s).symm.toContinuousLinearMap)

/-- The factoring `angularDirectionalDerivative s a = U ∘ M_s ∘ U⁻¹`, definitional because
`cyclesToAngular s = (angularWeightEquiv s).trans angularFrequencyDilation`. -/
theorem angularDirectionalDerivative_eq_dilation_mid (s : ℝ) (a : Space)
    (h : Lp ℂ 2 (volume : Measure Space)) :
    angularDirectionalDerivative s a h =
      angularFrequencyDilation (angularDirectionalMid s a (angularFrequencyDilation.symm h)) :=
  rfl

/-- The a.e. coefficient function of the middle operator is the three-way symbol product. -/
theorem angularDirectionalMid_coeFn (s : ℝ) (a : Space) (y : Lp ℂ 2 (volume : Measure Space)) :
    (angularDirectionalMid s a y : Space → ℂ) =ᵐ[volume] fun ξ =>
      (angularWeightSymbol (s - 1) ξ * sobolevDirectionalSymbol a ξ * angularWeightSymbol (-s) ξ)
        * y ξ := by
  have h1 : (angularDirectionalMid s a y : Space → ℂ) =ᵐ[volume] fun ξ =>
      angularWeightSymbol (s - 1) ξ *
        (sobolevDirectionalDerivative s a ((angularWeightEquiv s).symm y) : Space → ℂ) ξ :=
    angularWeightMap_coeFn (s - 1)
      (sobolevDirectionalDerivative s a ((angularWeightEquiv s).symm y))
  have h2 := sobolevDirectionalDerivative_coeFn s a ((angularWeightEquiv s).symm y)
  have h3 : ((angularWeightEquiv s).symm y : Space → ℂ) =ᵐ[volume]
      fun ξ => angularWeightSymbol (-s) ξ * y ξ := angularWeightMap_coeFn (-s) y
  filter_upwards [h1, h2, h3] with ξ e1 e2 e3
  rw [e1, e2, e3]
  ring

/-! ## 2. Skew-adjointness of the middle operator -/

/-- Skew-adjointness of `M_s` on `L²`: the middle symbol is purely imaginary
(`mid_symbol_imaginary`), so `⟪x, M_s y⟫ = -⟪M_s x, y⟫`. -/
theorem inner_angularDirectionalMid (s : ℝ) (a : Space)
    (x y : Lp ℂ 2 (volume : Measure Space)) :
    ⟪x, angularDirectionalMid s a y⟫_ℂ = -⟪angularDirectionalMid s a x, y⟫_ℂ := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def, ← MeasureTheory.integral_neg]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [angularDirectionalMid_coeFn s a y, angularDirectionalMid_coeFn s a x]
    with ξ hy hx
  simp only [RCLike.inner_apply, hy, hx]
  rw [map_mul, mid_symbol_imaginary]
  ring

/-! ## 3. Skew-adjointness of the angular directional derivative (the deliverable) -/

/-- **Skew-adjointness of `angularDirectionalDerivative`** on the `L²` carrier:
`⟪f, D_a g⟫ = -⟪D_a f, g⟫`.  Proved by transporting the skew-adjointness of the middle operator
`M_s` across the unitary dilation `U = angularFrequencyDilation` via
`LinearIsometryEquiv.inner_map_map`. -/
theorem inner_angularDirectionalDerivative_right (s : ℝ) (a : Space)
    (f g : Lp ℂ 2 (volume : Measure Space)) :
    ⟪f, angularDirectionalDerivative s a g⟫_ℂ = -⟪angularDirectionalDerivative s a f, g⟫_ℂ := by
  calc ⟪f, angularDirectionalDerivative s a g⟫_ℂ
      = ⟪angularFrequencyDilation (angularFrequencyDilation.symm f),
          angularFrequencyDilation
            (angularDirectionalMid s a (angularFrequencyDilation.symm g))⟫_ℂ := by
        rw [angularDirectionalDerivative_eq_dilation_mid,
          LinearIsometryEquiv.apply_symm_apply]
    _ = ⟪angularFrequencyDilation.symm f,
          angularDirectionalMid s a (angularFrequencyDilation.symm g)⟫_ℂ :=
        angularFrequencyDilation.inner_map_map _ _
    _ = -⟪angularDirectionalMid s a (angularFrequencyDilation.symm f),
          angularFrequencyDilation.symm g⟫_ℂ :=
        inner_angularDirectionalMid s a _ _
    _ = -⟪angularFrequencyDilation
            (angularDirectionalMid s a (angularFrequencyDilation.symm f)),
          angularFrequencyDilation (angularFrequencyDilation.symm g)⟫_ℂ := by
        rw [angularFrequencyDilation.inner_map_map]
    _ = -⟪angularDirectionalDerivative s a f, g⟫_ℂ := by
        rw [← angularDirectionalDerivative_eq_dilation_mid,
          LinearIsometryEquiv.apply_symm_apply]

/-! ## 4. Self-adjointness of the angular order-lowering operator (companion, required by step 3) -/

/-- The middle multiplication operator for `angularOrderLowering`:
`angularWeightEquiv r ∘ sobolevOrderLowering s r hrs ∘ (angularWeightEquiv s).symm`. -/
def angularOrderLoweringMid (s r : ℝ) (hrs : r ≤ s) :
    Lp ℂ 2 (volume : Measure Space) →L[ℂ] Lp ℂ 2 (volume : Measure Space) :=
  (angularWeightEquiv r).toContinuousLinearMap.comp
    ((sobolevOrderLowering s r hrs).comp (angularWeightEquiv s).symm.toContinuousLinearMap)

/-- The factoring `angularOrderLowering s r hrs = U ∘ L_s ∘ U⁻¹`, definitional for the same
reason as `angularDirectionalDerivative_eq_dilation_mid`. -/
theorem angularOrderLowering_eq_dilation_mid (s r : ℝ) (hrs : r ≤ s)
    (h : Lp ℂ 2 (volume : Measure Space)) :
    angularOrderLowering s r hrs h =
      angularFrequencyDilation (angularOrderLoweringMid s r hrs (angularFrequencyDilation.symm h)) :=
  rfl

/-- The a.e. coefficient function of the lowering middle operator is the three-way symbol product
`angularWeightSymbol r · sobolevBesselWeight (r-s) · angularWeightSymbol (-s)`. -/
theorem angularOrderLoweringMid_coeFn (s r : ℝ) (hrs : r ≤ s)
    (y : Lp ℂ 2 (volume : Measure Space)) :
    (angularOrderLoweringMid s r hrs y : Space → ℂ) =ᵐ[volume] fun ξ =>
      (angularWeightSymbol r ξ * sobolevBesselWeight (r - s) ξ * angularWeightSymbol (-s) ξ)
        * y ξ := by
  have h1 : (angularOrderLoweringMid s r hrs y : Space → ℂ) =ᵐ[volume] fun ξ =>
      angularWeightSymbol r ξ *
        (sobolevOrderLowering s r hrs ((angularWeightEquiv s).symm y) : Space → ℂ) ξ :=
    angularWeightMap_coeFn r (sobolevOrderLowering s r hrs ((angularWeightEquiv s).symm y))
  have h2 := sobolevOrderLowering_coeFn s r hrs ((angularWeightEquiv s).symm y)
  have h3 : ((angularWeightEquiv s).symm y : Space → ℂ) =ᵐ[volume]
      fun ξ => angularWeightSymbol (-s) ξ * y ξ := angularWeightMap_coeFn (-s) y
  filter_upwards [h1, h2, h3] with ξ e1 e2 e3
  rw [e1, e2, e3]
  ring

/-- Self-adjointness of the lowering middle operator on `L²`: the middle symbol is real
(`lowering_symbol_real`), so `⟪x, L y⟫ = ⟪L x, y⟫`. -/
theorem inner_angularOrderLoweringMid (s r : ℝ) (hrs : r ≤ s)
    (x y : Lp ℂ 2 (volume : Measure Space)) :
    ⟪x, angularOrderLoweringMid s r hrs y⟫_ℂ = ⟪angularOrderLoweringMid s r hrs x, y⟫_ℂ := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [angularOrderLoweringMid_coeFn s r hrs y, angularOrderLoweringMid_coeFn s r hrs x]
    with ξ hy hx
  simp only [RCLike.inner_apply, hy, hx]
  rw [map_mul, lowering_symbol_real]
  ring

/-- **Self-adjointness of `angularOrderLowering`** on the `L²` carrier:
`⟪f, L g⟫ = ⟪L f, g⟫`.  Same unitary transport as the directional derivative, with the real
middle symbol. -/
theorem inner_angularOrderLowering (s r : ℝ) (hrs : r ≤ s)
    (f g : Lp ℂ 2 (volume : Measure Space)) :
    ⟪f, angularOrderLowering s r hrs g⟫_ℂ = ⟪angularOrderLowering s r hrs f, g⟫_ℂ := by
  calc ⟪f, angularOrderLowering s r hrs g⟫_ℂ
      = ⟪angularFrequencyDilation (angularFrequencyDilation.symm f),
          angularFrequencyDilation
            (angularOrderLoweringMid s r hrs (angularFrequencyDilation.symm g))⟫_ℂ := by
        rw [angularOrderLowering_eq_dilation_mid, LinearIsometryEquiv.apply_symm_apply]
    _ = ⟪angularFrequencyDilation.symm f,
          angularOrderLoweringMid s r hrs (angularFrequencyDilation.symm g)⟫_ℂ :=
        angularFrequencyDilation.inner_map_map _ _
    _ = ⟪angularOrderLoweringMid s r hrs (angularFrequencyDilation.symm f),
          angularFrequencyDilation.symm g⟫_ℂ :=
        inner_angularOrderLoweringMid s r hrs _ _
    _ = ⟪angularFrequencyDilation
            (angularOrderLoweringMid s r hrs (angularFrequencyDilation.symm f)),
          angularFrequencyDilation (angularFrequencyDilation.symm g)⟫_ℂ := by
        rw [angularFrequencyDilation.inner_map_map]
    _ = ⟪angularOrderLowering s r hrs f, g⟫_ℂ := by
        rw [← angularOrderLowering_eq_dilation_mid, LinearIsometryEquiv.apply_symm_apply]

end NSFormalization.Paper3
