import NSFormalization.Section4.D01.LerayDatum
import NSFormalization.Section4.D01.HalfOrder
import NSFormalization.Section4.D01.Transverse
import NSFormalization.Section4.A04.LaplacianPairing
import NSFormalization.Section4.A04.RealPairing

/-!
# The Leray complement commutes with order lowering (D01 · P2 · SL7c)

`research/D01/P2_SPLIT.md` sub-lemma **SL7c** (bootstrap step of `eq:Rpressure`): the
Leray-complement multiplier on the manuscript datum carrier commutes with the angular
order-lowering operator.  Concretely, for `r ≤ s`,

  `lerayComplement r ∘ lowerVectorL s r hrs = lowerVectorL s r hrs ∘ lerayComplement s`,

i.e. the "shape of `sobolevRealization_orderLowering`": the `0`-homogeneous matrix symbol
`(I−P)` commutes with the scalar order weight.  This is what lets the order-`0` Plancherel seed
of `∇p` be bootstrapped to every order (SL7).

## Route (as executed; see `research/D01/ATTEMPTS_LERAY_LOWERING.md`)

Route **(b)** of the brief, the one that needs no `0`-homogeneity of the complex symbol: the
lowering is shown to be a plain a.e. Fourier **multiplier in the raw frequency variable**
(`angularOrderLowering_coeFn`), and a scalar multiplier commutes with any `ℂ`-linear fibre map
(`complementSymbolComplex ξ`) by `map_smul`.  The lowering's factoring `U ∘ M ∘ U⁻¹` through the
dilation `U = angularFrequencyDilation` (`A04.angularOrderLowering_eq_dilation_mid`,
`A04.angularOrderLoweringMid_coeFn`) is collapsed into the single raw multiplier
`loweringMult s r ξ = σ(frequencyUnit⁻¹ • ξ)` by feeding the dilation its own a.e. formula
`angularFrequencyDilation_coeFn` twice (substituting `h = U (U⁻¹ h)`), which cancels the
`c^{±3/2}` Jacobians without ever needing `U⁻¹`'s coefficient.  The dilation coefficient
`angularFrequencyDilation_coeFn` is reused from lane 079's merged
`Section4/D01/Transverse.lean` (same namespace `NSFormalization.Section4.D01`); it is not
re-proved here.

Contents:

* `assemble_vec_ae` (**exported helper**, three downstream lanes need it): the coeFn of `assemble`
  is a.e. the pointwise `PiLp` tuple of its scalar components.
* `loweringMult` / `angularOrderLowering_coeFn` — the lowering as a raw a.e. multiplier;
  `loweringMult_eq` / `angularOrderLowering_coeFn'` collapse it to the standard Bessel weight
  `(1+‖ξ‖²)^{(r−s)/2}` via lane 082's `RealPairing.lowering_mid_symbol_eq`.
* `lerayComplement_lowerVectorL` — the commutation lemma (the SL7c unit).
* `isSobolevDatum_lower` / `isSobolevDatum_lower_iff` / `leray_datum_lower` — the datum-transport
  interface SL7b/SL8 call (added on the lane-085 review, reviewer probe `/tmp/rev085_probe.lean`).

No `sorry`, no `axiom`; `#print axioms` is standard (`research/D01/axioms_leray_lowering.lean`).
-/

noncomputable section

namespace NSFormalization.Section4.D01.Leray

open Set MeasureTheory FourierTransform NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Section4.A03 (lowerDatum coe_lowerDatum isSobolevDatum_iff)
open NSFormalization.Source.RealSobolev (RealSobolevHilbert FourierData)
open NSFormalization.Source (frequencyUnit frequencyUnit_pos)
open NSFormalization.Source.FiniteHilbertBochner (assemble coordinates)
open scoped ENNReal SchwartzMap ComplexConjugate

/-! ## 1. `assemble` as a pointwise tuple (exported helper `assemble_vec_ae`) -/

/-- **The coeFn of `assemble` is a.e. its pointwise `PiLp` tuple.**  `(assemble 2 volume h) ξ`
equals a.e. the `EuclideanSpace ℂ (Fin 3)`-vector `fun j => (h j) ξ`.  Exported because SL5/SL7/SL8
all repackage `lerayComplement_ae`'s `assemble` argument this way. -/
theorem assemble_vec_ae (h : Fin 3 → Lp ℂ 2 (volume : Measure Space)) :
    (assemble 2 volume h : Space → MNS2.R3C) =ᵐ[volume]
      fun ξ => (WithLp.toLp 2 (fun j => (h j : Space → ℂ) ξ) : MNS2.R3C) := by
  have hall : ∀ᵐ ξ ∂(volume : Measure Space), ∀ j : Fin 3,
      (assemble 2 volume h ξ) j = (h j : Space → ℂ) ξ := by
    rw [ae_all_iff]
    intro j
    filter_upwards [coordinates_ae volume (assemble 2 volume h) j] with ξ hξ
    rw [coordinates_assemble volume h j] at hξ
    exact hξ.symm
  filter_upwards [hall] with ξ hξ
  apply PiLp.ext
  intro j
  rw [hξ j]

/-! ## 2. The order-lowering operator as a raw a.e. multiplier -/

/-- The raw-frequency multiplier symbol of `angularOrderLowering s r hrs`: the middle symbol
(`A04.angularOrderLoweringMid_coeFn`) evaluated at the pre-dilated frequency `frequencyUnit⁻¹ • ξ`.
The dilation Jacobians `c^{±3/2}` cancel, leaving exactly this scalar. -/
def loweringMult (s r : ℝ) (ξ : Space) : ℂ :=
  angularWeightSymbol r (frequencyUnit⁻¹ • ξ) * sobolevBesselWeight (r - s) (frequencyUnit⁻¹ • ξ)
    * angularWeightSymbol (-s) (frequencyUnit⁻¹ • ξ)

/-- **The angular order lowering is a plain a.e. Fourier multiplier.**  `angularOrderLowering
s r hrs h =ᵐ loweringMult s r · * h`.  Proved from the factoring `U ∘ M ∘ U⁻¹`
(`A04.angularOrderLowering_eq_dilation_mid`) by substituting `h = U (U⁻¹ h)` and applying the
dilation coefficient (`angularFrequencyDilation_coeFn`) on both `M (U⁻¹ h)` and `U⁻¹ h`, so the
`c^{±3/2}` factors cancel; the middle multiplier symbol is transported to `frequencyUnit⁻¹ • ξ`
via the quasi-measure-preserving dilation. -/
theorem angularOrderLowering_coeFn (s r : ℝ) (hrs : r ≤ s) (h : Lp ℂ 2 (volume : Measure Space)) :
    (angularOrderLowering s r hrs h : Space → ℂ) =ᵐ[volume]
      fun ξ => loweringMult s r ξ • h ξ := by
  have hqmp : Measure.QuasiMeasurePreserving
      (fun ξ : Space => frequencyUnit⁻¹ • ξ) volume volume := by
    refine ⟨(continuous_const_smul _).measurable, ?_⟩
    rw [Measure.map_addHaar_smul volume (inv_ne_zero frequencyUnit_pos.ne')]
    exact Measure.smul_absolutelyContinuous
  have hUM := angularFrequencyDilation_coeFn
    (angularOrderLoweringMid s r hrs (angularFrequencyDilation.symm h))
  have hUh := angularFrequencyDilation_coeFn (angularFrequencyDilation.symm h)
  rw [angularFrequencyDilation.apply_symm_apply] at hUh
  have hmid' := hqmp.ae (angularOrderLoweringMid_coeFn s r hrs (angularFrequencyDilation.symm h))
  rw [angularOrderLowering_eq_dilation_mid]
  filter_upwards [hUM, hmid', hUh] with ξ a1 a2 a3
  rw [a1, a2, a3]
  simp only [loweringMult, Complex.real_smul, smul_eq_mul]
  ring

/-- **The raw multiplier is the ordinary Bessel weight** (lane-085 review, finding 1).  The
three-factor `loweringMult` collapses to `(1+‖ξ‖²)^{(r−s)/2}` in the raw frequency variable: the
angular convention conjugates away entirely.  Proved from lane 082's closed form
`RealPairing.lowering_mid_symbol_eq` at the pre-dilated argument. -/
theorem loweringMult_eq (s r : ℝ) (ξ : Space) :
    loweringMult s r ξ = sobolevBesselWeight (r - s) ξ := by
  rw [loweringMult, lowering_mid_symbol_eq, smul_inv_smul₀ frequencyUnit_pos.ne']

/-- **The angular order lowering, as the ordinary Bessel multiplier.**  Simplified form of
`angularOrderLowering_coeFn` after `loweringMult_eq`: on the raw `L²` carrier the order lowering is
multiplication by the standard `(1+‖ξ‖²)^{(r−s)/2}`. -/
theorem angularOrderLowering_coeFn' (s r : ℝ) (hrs : r ≤ s)
    (h : Lp ℂ 2 (volume : Measure Space)) :
    (angularOrderLowering s r hrs h : Space → ℂ) =ᵐ[volume]
      fun ξ => sobolevBesselWeight (r - s) ξ • h ξ := by
  filter_upwards [angularOrderLowering_coeFn s r hrs h] with ξ hξ
  rw [hξ, loweringMult_eq]

/-- **Cross-check** (lane-085 review probe B): at `r = s` the multiplier is `1`, so the operator is
the identity — an independent re-derivation of A04's `RealPairing.angularOrderLowering_self`. -/
theorem angularOrderLowering_self_of_coeFn (s : ℝ) (h : Lp ℂ 2 (volume : Measure Space)) :
    angularOrderLowering s s le_rfl h = h := by
  apply Lp.ext
  filter_upwards [angularOrderLowering_coeFn' s s le_rfl h] with ξ hξ
  rw [hξ]
  simp [sobolevBesselWeight]

/-! ## 3. The commutation lemma (SL7c) -/

/-- Pulling a scalar through the complex complement fibre symbol, componentwise. -/
private theorem complementSymbolComplex_smul_apply (ξ : MNS2.R3) (c : ℂ) (v : MNS2.R3C)
    (i : Fin 3) :
    (complementSymbolComplex ξ (c • v)) i = c • ((complementSymbolComplex ξ v) i) := by
  rw [map_smul, PiLp.smul_apply]

/-- **The Leray complement commutes with order lowering (SL7c).**  On the manuscript datum
carrier, for `r ≤ s`, the order-lowering operator `lowerVectorL s r hrs` intertwines the
Leray-complement multipliers `lerayComplement s` and `lerayComplement r`.  The two agree because
the order weight acts a.e. as a **scalar** Fourier multiplier (`angularOrderLowering_coeFn`),
which the `ℂ`-linear fibre symbol `complementSymbolComplex ξ` pulls straight through. -/
theorem lerayComplement_lowerVectorL (s r : ℝ) (hrs : r ≤ s) (A : RealVectorSobolev s) :
    lerayComplement r (lowerVectorL s r hrs A) = lowerVectorL s r hrs (lerayComplement s A) := by
  apply PiLp.ext
  intro i
  apply Subtype.ext
  apply Lp.ext
  have hstar : ∀ᵐ ξ ∂(volume : Measure Space), ∀ j : Fin 3,
      (angularOrderLowering s r hrs ((A j : FourierData))) ξ
        = loweringMult s r ξ • ((A j : FourierData)) ξ := by
    rw [ae_all_iff]
    intro j
    exact angularOrderLowering_coeFn s r hrs (A j : FourierData)
  have hL : (fun ξ => (((lerayComplement r (lowerVectorL s r hrs A)) i : FourierData)) ξ)
      =ᵐ[volume] fun ξ => loweringMult s r ξ •
        (complementSymbolComplex ξ ((assemble 2 volume (fun j => ((A j : FourierData)))) ξ)) i := by
    filter_upwards [lerayComplement_ae r (lowerVectorL s r hrs A) i,
      assemble_vec_ae (fun j => ((A j : FourierData))),
      assemble_vec_ae (fun j => (((lowerVectorL s r hrs A) j : FourierData))),
      hstar] with ξ e1 eA eLo hs
    have hvec : (WithLp.toLp 2 (fun j => (((lowerVectorL s r hrs A) j : FourierData)) ξ) : MNS2.R3C)
        = loweringMult s r ξ • (WithLp.toLp 2 (fun j => (((A j : FourierData))) ξ) : MNS2.R3C) := by
      rw [← WithLp.toLp_smul]
      congr 1
      funext j
      exact hs j
    rw [e1, eLo, hvec, complementSymbolComplex_smul_apply, eA]
  have hR : (fun ξ => (((lowerVectorL s r hrs (lerayComplement s A)) i : FourierData)) ξ)
      =ᵐ[volume] fun ξ => loweringMult s r ξ •
        (complementSymbolComplex ξ ((assemble 2 volume (fun j => ((A j : FourierData)))) ξ)) i := by
    filter_upwards [angularOrderLowering_coeFn s r hrs ((lerayComplement s A) i : FourierData),
      lerayComplement_ae s A i] with ξ f1 f2
    show (angularOrderLowering s r hrs ((lerayComplement s A) i : FourierData)) ξ = _
    rw [f1, f2]
  exact hL.trans hR.symm

/-! ## 4. Datum transport (the SL7b/SL8 interface)

The three lemmas below are the datum-bookkeeping partners of the commutation, extracted on the
lane-085 review (reviewer probe `/tmp/rev085_probe.lean`, findings 2). `isSobolevDatum_lower` is
the standalone downward transport (previously only inline in `HalfOrder.isSobolevPath_lower`);
`isSobolevDatum_lower_iff` is the **iff** the SL7 bootstrap actually consumes (order-0 seed ⟹
order-`m`), free because `Paper3.angularRealization_orderLowering` is an equation; `leray_datum_lower`
chains the commutation with the transport. -/

/-- **Downward datum transport** (reviewer probe C): an order-`s` datum of `z` lowers to an
order-`r` datum of `z`, `r ≤ s`.  The single-time, standalone form of
`HalfOrder.isSobolevPath_lower`'s body. -/
theorem isSobolevDatum_lower {s r : ℝ} (hrs : r ≤ s) {z : Space → Space}
    {A : RealVectorSobolev s} (hA : IsSobolevDatum s z A) :
    IsSobolevDatum r z (lowerVectorL s r hrs A) := by
  rw [isSobolevDatum_iff]
  intro i
  rw [lowerVectorL_apply]
  exact ((isSobolevDatum_iff s _ A).mp hA i).lower hrs

/-- **Datum transport is an iff** (reviewer probe F): lowering preserves *and reflects* being an
order-datum of `z`, because `Paper3.angularRealization_orderLowering` is an equation (the lowered
datum realizes the same tempered distribution).  This is the direction the SL7 bootstrap needs:
an order-`r` seed of the lowering is exactly an order-`s` datum. -/
theorem isSobolevDatum_lower_iff {s r : ℝ} (hrs : r ≤ s) {z : Space → Space}
    {A : RealVectorSobolev s} :
    IsSobolevDatum r z (lowerVectorL s r hrs A) ↔ IsSobolevDatum s z A := by
  constructor
  · intro h i ψ
    have hiψ := h i ψ
    rw [lowerVectorL_apply, coe_lowerDatum, angularRealization_orderLowering] at hiψ
    exact hiψ
  · intro h
    exact isSobolevDatum_lower hrs h

/-- **The order-`r` Leray datum is the lowering of the order-`s` one** (reviewer probe E): combining
the commutation with `isSobolevDatum_lower`, no uniqueness hypothesis needed.  If `A` is an
order-`s` datum of `z` and `lerayComplement s A` is one of `w`, then `lerayComplement r` of the
lowered `A` is an order-`r` datum of `w`. -/
theorem leray_datum_lower {s r : ℝ} (hrs : r ≤ s) {z w : Space → Space}
    {A : RealVectorSobolev s} (_hA : IsSobolevDatum s z A)
    (htrans : IsSobolevDatum s w (lerayComplement s A)) :
    IsSobolevDatum r w (lerayComplement r (lowerVectorL s r hrs A)) := by
  rw [lerayComplement_lowerVectorL]
  exact isSobolevDatum_lower hrs htrans

end NSFormalization.Section4.D01.Leray
