import NSFormalization.Section4.D01.DerivativeDatum

/-!
# Fourier transverse form of a divergence-free field's datum (D01 · P2 · sub-lemma SL4)

`research/D01/P2_SPLIT.md` SL4 (Fourier transverse form) and
`research/D01/ATTEMPTS_SL4A.md` ("Transverse statement — precise gap").

For a divergence-free smooth square-integrable field `Z` and any order-`(m+1)` angular
Sobolev datum `A` of `Z.field`, the datum is **transverse** at a.e. frequency:
`∑ⱼ ξⱼ Â_j(ξ) = 0` a.e.  This is exactly the hypothesis
`NSFormalization.Section4.D01.Leray.complementSymbol_eq_zero_of_inner_eq_zero` consumes
to conclude `(I−P)` annihilates the field (SL4 of P2, `eq:Rhigh`/`eq:Rpressure`).

## Route (as executed; see `research/D01/ATTEMPTS_TRANSVERSE.md`)

* `isSobolevDatum_partialDeriv` (`DerivativeDatum.lean`) gives, for each `j`, the order-`m`
  datum `B_j` of `∂ⱼ Z.field`, whose `i`-th component is
  `angularDirectionalDerivativeReal (m+1) eⱼ (A i)`.
* The scalar `x ↦ ∑ⱼ (∂ⱼ Z.field x) j = div Z(x)` is identically `0`, so the diagonal
  datum `∑ⱼ (B_j j)` realizes the zero distribution; by injectivity of `angularRealization`
  it is `0` in `L²`.
* `angularDirectionalDerivative` is `cyclesToAngular (s-1) ∘ M ∘ (cyclesToAngular s).symm`
  (`M = sobolevDirectionalDerivative s eⱼ`); peeling the outer equivalence (injective) leaves
  `∑ⱼ M (kⱼ) = 0` with `kⱼ = (cyclesToAngular (m+1)).symm (A j)`.  The a.e. coefficient of `M`
  is `2πi ξⱼ (1+‖ξ‖²)^{-1/2}` (`sobolevDirectionalSymbol_..`), and `kⱼ`'s coefficient carries
  the extra factor `angularWeightSymbol (-(m+1))(ξ)`.  All three of
  `2πi`, `(1+‖ξ‖²)^{-1/2}`, `angularWeightSymbol (-(m+1))(ξ)` are pointwise nonzero, so they
  cancel and leave `∑ⱼ ξⱼ · (angularFrequencyDilation.symm (A j))(ξ) = 0` a.e.
  (`transverse_symm_of_divergence_free`, the cycles convention).
* Finally the angular convention (`(A j : FourierData)` directly): `angularFrequencyDilation`
  is the normalized `L²` frequency dilation `f ↦ c^{-3/2} f(c⁻¹·)`, `c = frequencyUnit`.  Its
  pointwise coefficient (`angularFrequencyDilation_coeFn`, proved here by identifying it with a
  `Lp.compMeasurePreserving` change of variables and matching distributions) plus the
  quasi-measure-preserving transport of the cycles statement by `c⁻¹·` upgrade the cycles form
  to the angular form (`transverse_of_divergence_free`).

No `sorry`, no `axiom`; `#print axioms` is standard (`research/D01/axioms_transverse.lean`).
-/

noncomputable section
open Set MeasureTheory FourierTransform NavierStokes.ProblemStatement
open EulerLpTranslation
open NSFormalization.Source.RealSobolev (RealSobolevHilbert FourierData)
open NSFormalization.Source.PhysicalSobolevDistribution
open NSFormalization.Source.PhysicalIntegerSobolev (componentField componentField_field)
open NSFormalization.Paper3
open NSFormalization.Section4.A03 (partialDeriv)
open NSFormalization.Source (frequencyUnit frequencyUnit_pos)
open scoped RealInnerProductSpace ComplexConjugate ENNReal SchwartzMap

namespace NSFormalization.Section4.D01

/-! ## 1. The pointwise coefficient of the normalized angular frequency dilation -/

/-- **Coefficient of the normalized `L²` frequency dilation.**  `angularFrequencyDilation`
is the normalized dilation `f ↦ c^{-3/2} f(c⁻¹·)`, `c = frequencyUnit`; it is defined as an
isometric extension, so this pointwise identity is proved by exhibiting the same operator as a
`Lp.compMeasurePreserving` change of variables (`map_addHaar_smul` supplies the Jacobian) and
matching their tempered-distribution actions.

This is a `Paper3`-level fact about `NSFormalization.Paper3.angularFrequencyDilation`; it lives
here only because lane 076 (merged, PR #78) supplies the *middle-multiplier* coefficient, not
the dilation's.  It is to be promoted to `Paper3/AngularFourierDilation.lean` by a SIMP lane
(lane 085 is copying it meanwhile); deduplicate in favour of the promoted lemma. -/
theorem angularFrequencyDilation_coeFn (h : Lp ℂ 2 (volume : Measure Space)) :
    (angularFrequencyDilation h : Space → ℂ) =ᵐ[volume]
      fun ξ => (frequencyUnit ^ (-3/2 : ℝ) : ℝ) • h (frequencyUnit⁻¹ • ξ) := by
  have hc0 : (0:ℝ) < frequencyUnit := frequencyUnit_pos
  set κ : ℝ≥0∞ := ENNReal.ofReal (|(frequencyUnit⁻¹ ^ (Module.finrank ℝ Space))⁻¹|) with hκ
  have hMP : MeasurePreserving (fun ξ : Space => frequencyUnit⁻¹ • ξ) volume (κ • volume) :=
    ⟨(continuous_const_smul _).measurable, Measure.map_addHaar_smul volume (inv_ne_zero hc0.ne')⟩
  have hGmem : MemLp (h : Space → ℂ) 2 (κ • volume) :=
    (Lp.memLp h).smul_measure (by rw [hκ]; exact ENNReal.ofReal_ne_top)
  set Dfwd : Lp ℂ 2 (volume : Measure Space) :=
    ((frequencyUnit ^ (-3/2 : ℝ) : ℝ)) •
      Lp.compMeasurePreserving (fun ξ : Space => frequencyUnit⁻¹ • ξ) hMP (hGmem.toLp _) with hDfwd
  have hDcoe : (Dfwd : Space → ℂ) =ᵐ[volume]
      fun ξ => (frequencyUnit ^ (-3/2:ℝ) : ℝ) • h (frequencyUnit⁻¹ • ξ) := by
    filter_upwards [Lp.coeFn_smul ((frequencyUnit ^ (-3/2:ℝ):ℝ) : ℝ)
        (Lp.compMeasurePreserving (fun ξ : Space => frequencyUnit⁻¹ • ξ) hMP (hGmem.toLp _)),
      Lp.coeFn_compMeasurePreserving (hGmem.toLp _) hMP,
      hMP.quasiMeasurePreserving.ae hGmem.coeFn_toLp] with ξ hs hcmp hgh
    rw [hDfwd, hs]
    simp only [Pi.smul_apply, hcmp, Function.comp_apply, hgh]
  have hfr3 : Module.finrank ℝ Space = 3 := by simp [Space]
  have hdist : (Dfwd : 𝓢'(Space, ℂ)) = (angularFrequencyDilation h : 𝓢'(Space, ℂ)) := by
    rw [angularFrequencyDilation_toDistribution]
    ext ψ
    rw [Lp.toTemperedDistribution_apply, angularDistributionDilation_apply,
      Lp.toTemperedDistribution_apply]
    rw [integral_congr_ae (hDcoe.mono (fun ξ hξ => by rw [hξ]))]
    have hcv := Measure.integral_comp_inv_smul (volume : Measure Space)
      (fun ξ => ψ (frequencyUnit • ξ) • ((frequencyUnit ^ (-3/2:ℝ) : ℝ) • h ξ)) frequencyUnit
    rw [hfr3] at hcv
    simp only [smul_inv_smul₀ hc0.ne'] at hcv
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ frequencyUnit ^ 3)] at hcv
    rw [hcv]
    rw [show (fun x : Space => ψ (frequencyUnit • x) • (frequencyUnit ^ (-3/2:ℝ) : ℝ) • (h x : ℂ))
          = (fun x : Space => (frequencyUnit ^ (-3/2:ℝ) : ℝ) • (ψ (frequencyUnit • x) • (h x : ℂ)))
          from by funext x; rw [smul_comm]]
    rw [integral_smul, ← mul_smul]
    congr 1
    · rw [← Real.rpow_natCast frequencyUnit 3, ← Real.rpow_add hc0]; norm_num
  have hi : Function.Injective (Lp.toTemperedDistributionCLM ℂ (volume : Measure Space) 2) :=
    LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot
  have hEq : Dfwd = angularFrequencyDilation h := hi hdist
  rw [← hEq]; exact hDcoe

/-! ## 2. The cycles-convention transverse form -/

/-- **Cycles-convention transversality.**  With `A` the order-`(m+1)` angular datum of a
divergence-free `Z`, the pre-dilation (cycles-convention) datum is transverse a.e.  This
is the full analytic content of SL4; `transverse_of_divergence_free` transports it to the
angular convention. -/
theorem transverse_symm_of_divergence_free {Z : SmoothL2Field Space}
    (hdiv : ∀ x : Space, ∑ j : Fin 3, partialDeriv j Z.field x j = 0)
    (m : ℕ) {A : RealVectorSobolev ((m : ℝ) + 1)}
    (hA : IsSobolevDatum ((m : ℝ) + 1) Z.field A) :
    ∀ᵐ ξ : Space ∂volume,
      ∑ j : Fin 3, ((ξ j : ℝ) : ℂ) *
        (angularFrequencyDilation.symm (A j : FourierData)) ξ = 0 := by
  set g : Fin 3 → FourierData := fun j => angularFrequencyDilation.symm (A j : FourierData) with hg
  have hXfield : ∀ (j : Fin 3) (x : Space),
      ((componentField j Z).directionalField (coordinateVector j)).field x
        = ((partialDeriv j Z.field x j : ℝ) : ℂ) := by
    intro j x
    rw [← componentField_directionalField]
    simp only [componentField_field, EulerLpTranslation.SmoothL2Field.directionalField_field]
    rfl
  have hreal : ∀ j : Fin 3,
      angularRealization (m : ℝ)
        (angularDirectionalDerivative ((m : ℝ) + 1) (coordinateVector j) (A j : FourierData))
        = physicalDistribution ((componentField j Z).directionalField (coordinateVector j)) := by
    intro j
    ext ψ
    have hcoe : angularDirectionalDerivative ((m : ℝ) + 1) (coordinateVector j) (A j : FourierData)
        = ((WithLp.toLp 2 fun i =>
            angularDirectionalDerivativeReal ((m : ℝ) + 1) (coordinateVector j) (A i)) j :
              RealSobolevHilbert (m : ℝ)) :=
      (angularDirectionalDerivativeReal_coe ((m : ℝ) + 1) (coordinateVector j) (A j)).symm
    rw [hcoe, (isSobolevDatum_partialDeriv j m hA) j ψ, physicalDistribution_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [hXfield, smul_eq_mul]
  have hsum0 : (∑ j : Fin 3,
      angularDirectionalDerivative ((m : ℝ) + 1) (coordinateVector j) (A j : FourierData)) = 0 := by
    apply (angularRealization_injective (m : ℝ))
    rw [map_sum, map_zero]
    ext ψ
    rw [sum_apply, IsZeroApply.zero_apply]
    have hint : ∀ j : Fin 3, Integrable
        (fun x => ψ x • ((componentField j Z).directionalField (coordinateVector j)).field x) volume :=
      fun j => schwartz_smul_field_integrable _ ψ
    calc ∑ j : Fin 3,
            angularRealization (m : ℝ)
              (angularDirectionalDerivative ((m : ℝ) + 1) (coordinateVector j) (A j : FourierData)) ψ
        = ∑ j : Fin 3,
            ∫ x, ψ x • ((componentField j Z).directionalField (coordinateVector j)).field x := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [hreal j, physicalDistribution_apply]
      _ = ∫ x, ∑ j : Fin 3,
            ψ x • ((componentField j Z).directionalField (coordinateVector j)).field x := by
          rw [← integral_finsetSum _ (fun j _ => hint j)]
      _ = 0 := by
          rw [← integral_zero (α := Space) (G := ℂ)]
          refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
          simp only [hXfield, ← Finset.smul_sum]
          rw [← Complex.ofReal_sum, hdiv x, Complex.ofReal_zero, smul_zero]
  have hpeel : (∑ j : Fin 3, sobolevDirectionalDerivative ((m : ℝ) + 1) (coordinateVector j)
        (angularWeightEquiv (-((m : ℝ) + 1)) (g j))) = 0 := by
    apply (cyclesToAngular ((m : ℝ) + 1 - 1)).injective
    rw [map_zero, map_sum]
    exact hsum0
  set F : Fin 3 → FourierData :=
    fun j => sobolevDirectionalDerivative ((m : ℝ) + 1) (coordinateVector j)
      (angularWeightEquiv (-((m : ℝ) + 1)) (g j)) with hF
  have hz : ⇑(∑ j : Fin 3, F j) =ᵐ[volume] 0 := by rw [hpeel]; exact Lp.coeFn_zero ℂ 2 volume
  have hFcoe : ∀ j : Fin 3,
      ⇑(F j) =ᵐ[volume] fun ξ => sobolevDirectionalSymbol (coordinateVector j) ξ *
        (angularWeightSymbol (-((m : ℝ) + 1)) ξ * (g j) ξ) := by
    intro j
    filter_upwards [sobolevDirectionalDerivative_coeFn ((m : ℝ) + 1) (coordinateVector j)
        (angularWeightEquiv (-((m : ℝ) + 1)) (g j)),
      angularWeightEquiv_coeFn (-((m : ℝ) + 1)) (g j)] with ξ h1 h2
    rw [hF]
    simp only
    rw [h1, h2]
  filter_upwards [hz, Lp.coeFn_add (F 0 + F 1) (F 2), Lp.coeFn_add (F 0) (F 1),
    hFcoe 0, hFcoe 1, hFcoe 2] with ξ hz0 hadd2 hadd1 hf0 hf1 hf2
  have hW : sobolevBesselWeight (-1) ξ ≠ 0 := by
    simp only [sobolevBesselWeight]; rw [Complex.ofReal_ne_zero]; positivity
  have hAW : angularWeightSymbol (-((m : ℝ) + 1)) ξ ≠ 0 := by
    simp only [angularWeightSymbol, sobolevBesselWeight]
    rw [mul_ne_zero_iff]; constructor <;> · rw [Complex.ofReal_ne_zero]; positivity
  have hσ : ∀ j : Fin 3, sobolevDirectionalSymbol (coordinateVector j) ξ
      = (2 * (Real.pi : ℂ) * Complex.I) * (((ξ j : ℝ) : ℂ) * sobolevBesselWeight (-1) ξ) := by
    intro j
    rw [sobolevDirectionalSymbol]
    congr 3
    rw [coordinateVector, EuclideanSpace.inner_single_right]; simp
  have hexp : (F 0) ξ + (F 1) ξ + (F 2) ξ = 0 := by
    have := hz0
    rw [show (∑ j : Fin 3, F j) = F 0 + F 1 + F 2 from by rw [Fin.sum_univ_three]] at this
    rw [hadd2, Pi.add_apply, hadd1, Pi.add_apply] at this
    simpa using this
  rw [hf0, hf1, hf2, hσ 0, hσ 1, hσ 2] at hexp
  set C : ℂ := (2 * (Real.pi : ℂ) * Complex.I) * sobolevBesselWeight (-1) ξ
      * angularWeightSymbol (-((m : ℝ) + 1)) ξ with hC
  have hCne : C ≠ 0 := by
    rw [hC]
    refine mul_ne_zero (mul_ne_zero ?_ hW) hAW
    simp [Complex.I_ne_zero, Real.pi_ne_zero]
  rw [Fin.sum_univ_three]
  have hfactor : C * (((ξ 0 : ℝ) : ℂ) * (g 0) ξ + ((ξ 1 : ℝ) : ℂ) * (g 1) ξ
      + ((ξ 2 : ℝ) : ℂ) * (g 2) ξ) = 0 := by
    rw [hC]; ring_nf; ring_nf at hexp; linear_combination hexp
  exact (mul_eq_zero.mp hfactor).resolve_left hCne

/-! ## 3. The angular-convention transverse form (the SL4 deliverable) -/

/-- **Fourier transverse form (SL4).**  A divergence-free smooth square-integrable field has a.e.
transverse Fourier data at every order: `∑ⱼ ξⱼ Â_j(ξ) = 0` a.e., where `A` is any order-`(m+1)`
angular Sobolev datum of `Z.field`.  Fed to
`Leray.complementSymbol_eq_zero_of_inner_eq_zero`, this shows `(I−P)` annihilates the field
(P2, `eq:Rhigh`/`eq:Rpressure`). -/
theorem transverse_of_divergence_free {Z : SmoothL2Field Space}
    (hdiv : ∀ x : Space, ∑ j : Fin 3, partialDeriv j Z.field x j = 0)
    (m : ℕ) {A : RealVectorSobolev ((m : ℝ) + 1)}
    (hA : IsSobolevDatum ((m : ℝ) + 1) Z.field A) :
    ∀ᵐ ξ : Space ∂volume,
      ∑ j : Fin 3, ((ξ j : ℝ) : ℂ) * ((A j : FourierData) ξ) = 0 := by
  have hc0 : (0:ℝ) < frequencyUnit := frequencyUnit_pos
  have hstar := transverse_symm_of_divergence_free hdiv m hA
  set κ : ℝ≥0∞ := ENNReal.ofReal (|(frequencyUnit⁻¹ ^ (Module.finrank ℝ Space))⁻¹|) with hκ
  have hMP : MeasurePreserving (fun ξ : Space => frequencyUnit⁻¹ • ξ) volume (κ • volume) :=
    ⟨(continuous_const_smul _).measurable, Measure.map_addHaar_smul volume (inv_ne_zero hc0.ne')⟩
  have htrans : ∀ᵐ ξ : Space ∂volume,
      (∑ j : Fin 3, (((frequencyUnit⁻¹ • ξ) j : ℝ) : ℂ) *
        (angularFrequencyDilation.symm (A j : FourierData)) (frequencyUnit⁻¹ • ξ)) = 0 :=
    hMP.quasiMeasurePreserving.ae (Measure.ae_smul_measure hstar κ)
  have hfwd : ∀ j : Fin 3, ∀ᵐ ξ : Space ∂volume,
      ((A j : FourierData) ξ) = (frequencyUnit ^ (-3/2:ℝ) : ℝ) •
        (angularFrequencyDilation.symm (A j : FourierData)) (frequencyUnit⁻¹ • ξ) := by
    intro j
    have h1 := angularFrequencyDilation_coeFn (angularFrequencyDilation.symm (A j : FourierData))
    rw [LinearIsometryEquiv.apply_symm_apply] at h1
    exact h1
  filter_upwards [htrans, hfwd 0, hfwd 1, hfwd 2] with ξ ht h0 h1 h2
  have hsmul : ∀ j : Fin 3, ((frequencyUnit⁻¹ • ξ) j : ℝ) = frequencyUnit⁻¹ * ξ j :=
    fun j => rfl
  rw [Fin.sum_univ_three, h0, h1, h2]
  rw [Fin.sum_univ_three] at ht
  simp only [hsmul, Complex.ofReal_mul, Complex.real_smul] at ht ⊢
  have hcinv : ((frequencyUnit⁻¹ : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact inv_ne_zero hc0.ne'
  have hgs : ((ξ 0 : ℝ) : ℂ) * (angularFrequencyDilation.symm (A 0 : FourierData)) (frequencyUnit⁻¹ • ξ)
      + ((ξ 1 : ℝ) : ℂ) * (angularFrequencyDilation.symm (A 1 : FourierData)) (frequencyUnit⁻¹ • ξ)
      + ((ξ 2 : ℝ) : ℂ) * (angularFrequencyDilation.symm (A 2 : FourierData)) (frequencyUnit⁻¹ • ξ) = 0 := by
    have h := ht
    have : ((frequencyUnit⁻¹ : ℝ) : ℂ) * (((ξ 0 : ℝ) : ℂ) * (angularFrequencyDilation.symm (A 0 : FourierData)) (frequencyUnit⁻¹ • ξ)
        + ((ξ 1 : ℝ) : ℂ) * (angularFrequencyDilation.symm (A 1 : FourierData)) (frequencyUnit⁻¹ • ξ)
        + ((ξ 2 : ℝ) : ℂ) * (angularFrequencyDilation.symm (A 2 : FourierData)) (frequencyUnit⁻¹ • ξ)) = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp this).resolve_left hcinv
  linear_combination ((frequencyUnit ^ (-3/2:ℝ) : ℝ) : ℂ) * hgs

end NSFormalization.Section4.D01
