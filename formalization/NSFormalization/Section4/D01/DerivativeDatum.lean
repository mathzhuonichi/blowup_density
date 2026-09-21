import NSFormalization.Paper3.SobolevDirectionalDerivative
import NSFormalization.Paper3.AngularTameProduct
import NSFormalization.Paper3.AngularRealSobolev
import NSFormalization.Section4.D01.SmoothDatum
import NSFormalization.Section4.A03.OuterTameProduct

/-!
# The order-`m` angular datum of a spatial partial derivative (unit D01, shared A04/SL3 · D01/P2)

`research/A04/G1_SPLIT.md` §SL3 and `research/D01/REVIEW_P2.md`'s `∂ⱼ`-datum both need
one fact: on the manuscript's angular datum carrier
`RealVectorSobolev s = Product (Fin 3) (RealSobolevHilbert s)`, the order-`m` datum of a
partial derivative `∂ⱼz` is a fixed **bounded Fourier multiplier** of the order-`(m+1)`
datum of `z` — the multiplier by the angular symbol `iξⱼ (1+‖ξ‖²)^{-1/2}`.  Because that
symbol is purely imaginary and odd, it maps the conjugate-reflection real subspace to
itself; because it is bounded (`|ξⱼ| ≤ ‖ξ‖ ≤ (1+‖ξ‖²)^{1/2}`) it is a genuine CLM lowering
the Sobolev order by one.

Rather than rebuild the L∞-multiplier from scratch, the operator is the existing cycles
directional-derivative CLM `Paper3.sobolevDirectionalDerivative`
(`SobolevDirectionalDerivative.lean:53`, symbol `2πi⟨ξ,a⟩(1+‖ξ‖²)^{-1/2}`) conjugated by
the cycles↔angular equivalence `Paper3.cyclesToAngular`, exactly as
`Paper3.angularOrderLowering` conjugates `Paper3.sobolevOrderLowering`
(`AngularTameProduct.lean:39`).  Conjugation gives the physical-distribution realization
`angularRealization (s-1) (D h) = ∂_a (angularRealization s h)` for free from
`Paper3.sobolevRealization_directionalDerivative`, and reality preservation transports from
`Paper3.cyclesToAngular_realSymmetry` once the cycles operator is shown to commute with
conjugate reflection (the symbol identity `conj (σ(-ξ)) = σ(ξ)`).

The payoff for A04/SL3 and D01/P2 is `isSobolevDatum_partialDeriv`: for a smooth
square-integrable field `Z` (`EulerLpTranslation.SmoothL2Field`, the slice class of
`ClassicalSolutionR`, `D01/Pressure.lean:velocity_slice_smoothL2`) and any order-`(m+1)`
datum `A` of `Z.field`, the componentwise real directional-derivative operator produces an
order-`m` datum of `A03.partialDeriv j Z.field`.

## What is *not* here (the remaining SL3 gap)

The dissipation identity `⟪G, datum Δu⟫_{H^m} = -‖∇u‖²_{H^m}` (`G1_SPLIT.md:129`) additionally
needs (i) the angular operator's **skew-adjointness** w.r.t. the `L²` inner product — true
because the symbol is purely imaginary, but requiring its a.e. coefficient function, not
proved here — (ii) the Laplacian datum assembled as `∑ⱼ D∘D` of the order-`(m+2)` datum with
the angular order-lowering interplay, and (iii) the `gradientSobolevNormAt` identification.
`A04/LaplacianDatum.lean` records those precisely; this module closes the derivative-datum
step both share.
-/

noncomputable section

open Set MeasureTheory FourierTransform NavierStokes.ProblemStatement
open EulerLpTranslation EulerLpTranslation.SmoothL2Field
open NSFormalization.Source.RealSobolev (RealSobolevHilbert FourierData)
open NSFormalization.Source (frequencyUnit)
open scoped ENNReal SchwartzMap LineDeriv ComplexConjugate

namespace NSFormalization.Paper3

/-! ## 1. The angular directional-derivative multiplier -/

/-- The angular directional-derivative operator: conjugate the cycles operator
`sobolevDirectionalDerivative` by the cycles-to-angular equivalence, exactly as
`angularOrderLowering` conjugates `sobolevOrderLowering`. -/
def angularDirectionalDerivative (s : ℝ) (a : Space) :
    Lp ℂ 2 (volume : Measure Space) →L[ℂ] Lp ℂ 2 (volume : Measure Space) :=
  (cyclesToAngular (s - 1)).toContinuousLinearMap.comp
    ((sobolevDirectionalDerivative s a).comp (cyclesToAngular s).symm.toContinuousLinearMap)

/-- It realizes the actual distributional directional derivative in the angular
convention.  Transport of `sobolevRealization_directionalDerivative`. -/
theorem angularRealization_directionalDerivative (s : ℝ) (a : Space)
    (h : Lp ℂ 2 (volume : Measure Space)) :
    angularRealization (s - 1) (angularDirectionalDerivative s a h) =
      ∂_{a} (angularRealization s h) := by
  change angularRealization (s - 1) (cyclesToAngular (s - 1)
    (sobolevDirectionalDerivative s a ((cyclesToAngular s).symm h))) = _
  rw [angularRealization_cyclesToAngular, sobolevRealization_directionalDerivative,
    angularRealization_eq_cycles]

/-! ## 2. Reality preservation -/

/-- The directional-derivative symbol is odd-imaginary: conjugate reflection fixes it,
`conj (σ(-ξ)) = σ(ξ)`.  This is the reason `iξⱼ` maps real (conjugate-symmetric) data to
real data. -/
theorem conj_sobolevDirectionalSymbol_neg (a ξ : Space) :
    conj (sobolevDirectionalSymbol a (-ξ)) = sobolevDirectionalSymbol a ξ := by
  simp only [sobolevDirectionalSymbol, sobolevBesselWeight, norm_neg,
    inner_neg_left, Complex.ofReal_neg, map_mul, map_neg, Complex.conj_I,
    Complex.conj_ofReal, map_ofNat]
  ring

/-- The cycles directional derivative commutes with conjugate reflection. -/
theorem realSymmetry_sobolevDirectionalDerivative (s : ℝ) (a : Space)
    (h : SobolevHilbert s) :
    Source.RealSobolev.realSymmetry (sobolevDirectionalDerivative s a h) =
      sobolevDirectionalDerivative s a (Source.RealSobolev.realSymmetry h) := by
  apply Lp.ext
  have hr := (Measure.measurePreserving_neg (volume : Measure Space)).quasiMeasurePreserving.ae
    (sobolevDirectionalDerivative_coeFn s a h)
  filter_upwards [Source.RealSobolev.realSymmetry_ae (sobolevDirectionalDerivative s a h),
    sobolevDirectionalDerivative_coeFn s a (Source.RealSobolev.realSymmetry h),
    Source.RealSobolev.realSymmetry_ae h, hr] with ξ h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄, map_mul, conj_sobolevDirectionalSymbol_neg]

/-- Conjugate reflection commutes through the inverse of `cyclesToAngular`. -/
theorem cyclesToAngular_symm_realSymmetry (s : ℝ) (h : Lp ℂ 2 (volume : Measure Space)) :
    (cyclesToAngular s).symm (Source.RealSobolev.realSymmetry h) =
      Source.RealSobolev.realSymmetry ((cyclesToAngular s).symm h) := by
  apply (cyclesToAngular s).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, ← cyclesToAngular_realSymmetry,
    ContinuousLinearEquiv.apply_symm_apply]

/-- The angular directional derivative commutes with conjugate reflection. -/
theorem realSymmetry_angularDirectionalDerivative (s : ℝ) (a : Space)
    (h : Lp ℂ 2 (volume : Measure Space)) :
    Source.RealSobolev.realSymmetry (angularDirectionalDerivative s a h) =
      angularDirectionalDerivative s a (Source.RealSobolev.realSymmetry h) := by
  change Source.RealSobolev.realSymmetry (cyclesToAngular (s - 1)
      (sobolevDirectionalDerivative s a ((cyclesToAngular s).symm h))) =
    cyclesToAngular (s - 1) (sobolevDirectionalDerivative s a
      ((cyclesToAngular s).symm (Source.RealSobolev.realSymmetry h)))
  rw [cyclesToAngular_realSymmetry, realSymmetry_sobolevDirectionalDerivative,
    cyclesToAngular_symm_realSymmetry]

/-- Reality preservation on the closed real subspace. -/
theorem angularDirectionalDerivative_mem_realSubspace (s : ℝ) (a : Space)
    {h : Lp ℂ 2 (volume : Measure Space)} (hh : h ∈ Source.RealSobolev.realSubspace s) :
    angularDirectionalDerivative s a h ∈ Source.RealSobolev.realSubspace (s - 1) := by
  rw [Source.RealSobolev.mem_realSubspace_iff, realSymmetry_angularDirectionalDerivative,
    (Source.RealSobolev.mem_realSubspace_iff s h).mp hh]

/-! ## 3. The real-restricted operator -/

/-- The manuscript-carrier directional-derivative multiplier: a real CLM on the angular
real Sobolev subspace, lowering the order by one. -/
def angularDirectionalDerivativeReal (s : ℝ) (a : Space) :
    RealSobolevHilbert s →L[ℝ] RealSobolevHilbert (s - 1) :=
  (((angularDirectionalDerivative s a).restrictScalars ℝ).comp
      (Source.RealSobolev.realSubspace s).toSubmodule.subtypeL).codRestrict
    (Source.RealSobolev.realSubspace (s - 1)).toSubmodule
    (fun x => angularDirectionalDerivative_mem_realSubspace s a x.2)

@[simp] theorem angularDirectionalDerivativeReal_coe (s : ℝ) (a : Space)
    (h : RealSobolevHilbert s) :
    ((angularDirectionalDerivativeReal s a h : RealSobolevHilbert (s - 1))
        : Source.RealSobolev.FourierData) =
      angularDirectionalDerivative s a (h : Source.RealSobolev.FourierData) := rfl


/-! ## 3.5 Symbol facts for the SL3 pairing identity (machine-checked, for the next lane)

`angularDirectionalDerivative s a = U ∘ M_s ∘ U⁻¹` with `U = angularFrequencyDilation` a
`LinearIsometryEquiv` (unitary) and `M_s = W_{s-1} ∘ σ_a ∘ W_{-s}` a product of three
multiplication operators (`angularWeightMap (s-1)`, `sobolevDirectionalDerivative s a`,
`angularWeightMap (-s) = (angularWeightEquiv s).symm`).  The SL3 pairing identity
`⟪G, datum Δu⟫ = -‖∇u‖²` reduces to the skew-adjointness of `M_s` on `L²`, which follows from
these pointwise symbol facts (`conj σ = -σ` for the directional middle symbol, `conj w = w`
for the lowering one) via `MeasureTheory.L2.inner_def` + `integral_congr_ae`; the transport
across the unitary `U` is `LinearIsometryEquiv.inner_map_map`, needing no dilation coefficient
function.  `mid_symbol_order_independent` shows all `angularDirectionalDerivative s a` are the
same operator, so the order-`m/m+1/m+2` bookkeeping of the Laplacian datum collapses. -/

/-- The cycles directional symbol `2πi⟨ξ,a⟩(1+‖ξ‖²)^{-1/2}` is purely imaginary. -/
theorem cycles_symbol_imaginary (a ξ : Space) :
    conj (sobolevDirectionalSymbol a ξ) = -(sobolevDirectionalSymbol a ξ) := by
  simp only [sobolevDirectionalSymbol, sobolevBesselWeight, map_mul, Complex.conj_I,
    Complex.conj_ofReal, map_ofNat]
  ring

/-- The angular Bessel weight symbol is real (conjugate reflection fixes it pointwise). -/
theorem angularWeightSymbol_conj (s : ℝ) (ξ : Space) :
    conj (angularWeightSymbol s ξ) = angularWeightSymbol s ξ := by
  simp only [angularWeightSymbol, sobolevBesselWeight, map_mul, Complex.conj_ofReal]

/-- **Reality of the lowering middle symbol.**  The middle symbol of `angularOrderLowering`,
`W_r · (1+‖ξ‖²)^{(r-s)/2} · W_{-s}`, is real, so `angularOrderLowering` is self-adjoint on `L²`. -/
theorem lowering_symbol_real (s r : ℝ) (ξ : Space) :
    conj (angularWeightSymbol r ξ * sobolevBesselWeight (r - s) ξ * angularWeightSymbol (-s) ξ) =
      angularWeightSymbol r ξ * sobolevBesselWeight (r - s) ξ * angularWeightSymbol (-s) ξ := by
  simp only [map_mul, angularWeightSymbol, sobolevBesselWeight, Complex.conj_ofReal]

/-- **Pure imaginarity of the directional middle symbol.**  The middle symbol of
`angularDirectionalDerivative`, `W_{s-1} · σ_a · W_{-s}`, is purely imaginary, so
`angularDirectionalDerivative` is skew-adjoint on `L²`. -/
theorem mid_symbol_imaginary (s : ℝ) (a ξ : Space) :
    conj (angularWeightSymbol (s - 1) ξ * sobolevDirectionalSymbol a ξ *
        angularWeightSymbol (-s) ξ) =
      -(angularWeightSymbol (s - 1) ξ * sobolevDirectionalSymbol a ξ * angularWeightSymbol (-s) ξ) := by
  rw [map_mul, map_mul, angularWeightSymbol_conj, angularWeightSymbol_conj, cycles_symbol_imaginary]
  ring

/-- The two Bessel weight factors of the directional middle symbol collapse to a symbol
independent of the order. -/
theorem weight_product_order_indep (s : ℝ) (ξ : Space) :
    angularWeightSymbol (s - 1) ξ * angularWeightSymbol (-s) ξ =
      sobolevBesselWeight (-1) (frequencyUnit • ξ) * sobolevBesselWeight 1 ξ := by
  have h1 := congrFun (sobolevBesselWeight_mul (s - 1) (-s)) (frequencyUnit • ξ)
  have h2 := congrFun (sobolevBesselWeight_mul (-(s - 1)) s) ξ
  simp only [Pi.mul_apply] at h1 h2
  unfold angularWeightSymbol
  simp only [neg_neg]
  rw [mul_mul_mul_comm, h1, h2, show s - 1 + -s = (-1 : ℝ) from by ring,
    show -(s - 1) + s = (1 : ℝ) from by ring]

/-- **Order-independence of the middle operator.**  The directional middle symbol
`W_{s-1} · σ_a · W_{-s}` does not depend on `s`; hence every `angularDirectionalDerivative s a`
is the *same* map (the `angularFrequencyDilation` conjugation does not depend on `s` either),
so the Laplacian-datum order bookkeeping between orders `m`, `m+1`, `m+2` is vacuous. -/
theorem mid_symbol_order_independent (s t : ℝ) (a ξ : Space) :
    angularWeightSymbol (s - 1) ξ * sobolevDirectionalSymbol a ξ * angularWeightSymbol (-s) ξ =
      angularWeightSymbol (t - 1) ξ * sobolevDirectionalSymbol a ξ * angularWeightSymbol (-t) ξ := by
  have hs := weight_product_order_indep s ξ
  have ht := weight_product_order_indep t ξ
  rw [mul_right_comm (angularWeightSymbol (s - 1) ξ) (sobolevDirectionalSymbol a ξ)
        (angularWeightSymbol (-s) ξ),
    mul_right_comm (angularWeightSymbol (t - 1) ξ) (sobolevDirectionalSymbol a ξ)
        (angularWeightSymbol (-t) ξ),
    hs, ht]


end NSFormalization.Paper3

/-! ## 4. The derivative datum (shared A04/SL3 · D01/P2) -/

namespace NSFormalization.Section4.D01

open NSFormalization.Paper3
open NSFormalization.Source.PhysicalSobolevDistribution
open NSFormalization.Source.PhysicalIntegerSobolev (componentField componentField_field)
open NSFormalization.Section4.A03 (partialDeriv)

/-- The angular order-`s` datum of a field realizes the physical tempered distribution of
the corresponding scalar component. -/
theorem angularRealization_of_isSobolevDatum {Z : SmoothL2Field Space} {s : ℝ}
    {A : RealVectorSobolev s} (hA : IsSobolevDatum s Z.field A) (i : Fin 3) :
    angularRealization s ((A i : FourierData)) = physicalDistribution (componentField i Z) := by
  ext φ
  rw [physicalDistribution_apply]
  simp only [componentField_field, smul_eq_mul]
  exact hA i φ

/-- **Derivative datum.**  For a smooth square-integrable field `Z` and any order-`(m+1)`
angular datum `A` of `Z.field`, the componentwise real directional-derivative multiplier
`angularDirectionalDerivativeReal` produces an order-`m` angular datum of the physical
partial derivative `A03.partialDeriv j Z.field`.  This is the multiplier-form statement
that A04/SL3 and D01/P2 both consume:  `datum_m(∂ⱼz) = (iξⱼ (1+‖ξ‖²)^{-1/2}) · datum_{m+1}(z)`. -/
theorem isSobolevDatum_partialDeriv {Z : SmoothL2Field Space} (j : Fin 3) (m : ℕ)
    {A : RealVectorSobolev ((m : ℝ) + 1)} (hA : IsSobolevDatum ((m : ℝ) + 1) Z.field A) :
    IsSobolevDatum (m : ℝ) (partialDeriv j Z.field)
      (WithLp.toLp 2 fun i =>
        angularDirectionalDerivativeReal ((m : ℝ) + 1) (coordinateVector j) (A i)) := by
  intro i ψ
  have horder : (m : ℝ) + 1 - 1 = (m : ℝ) := by ring
  have hrel := angularRealization_directionalDerivative ((m : ℝ) + 1) (coordinateVector j)
    ((A i : FourierData))
  rw [horder] at hrel
  have hBi : (((WithLp.toLp 2 fun k =>
        angularDirectionalDerivativeReal ((m : ℝ) + 1) (coordinateVector j) (A k)) i :
          RealSobolevHilbert (m : ℝ)) : FourierData) =
      angularDirectionalDerivative ((m : ℝ) + 1) (coordinateVector j) ((A i : FourierData)) :=
    angularDirectionalDerivativeReal_coe ((m : ℝ) + 1) (coordinateVector j) (A i)
  calc angularRealization (m : ℝ)
        (((WithLp.toLp 2 fun k =>
          angularDirectionalDerivativeReal ((m : ℝ) + 1) (coordinateVector j) (A k)) i :
            RealSobolevHilbert (m : ℝ)) : FourierData) ψ
      = (∂_{coordinateVector j}
          (angularRealization ((m : ℝ) + 1) ((A i : FourierData)))) ψ := by rw [hBi, hrel]
    _ = (∂_{coordinateVector j} (physicalDistribution (componentField i Z))) ψ := by
          rw [angularRealization_of_isSobolevDatum hA i]
    _ = physicalDistribution ((componentField i Z).directionalField (coordinateVector j)) ψ := by
          rw [physicalDistribution_directionalField]
    _ = ∫ x, ψ x • ((componentField i Z).directionalField (coordinateVector j)).field x :=
          physicalDistribution_apply _ _
    _ = ∫ x, ψ x * ((partialDeriv j Z.field x i : ℝ) : ℂ) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [smul_eq_mul, ← componentField_directionalField]
          simp only [componentField_field, directionalField_field]
          rfl

end NSFormalization.Section4.D01
