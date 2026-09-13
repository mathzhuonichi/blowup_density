import NSFormalization.Section4.D01.Transverse
import NSFormalization.Section4.D01.LerayDatum

/-!
# Fourier longitudinal form of a curl-free field's datum (D01 · P2 · sub-lemma SL5)

`research/D01/P2_SPLIT.md` SL5 (gradient longitudinal via curl-freeness) and
`research/D01/ATTEMPTS_LONGITUDINAL.md`.

For a smooth square-integrable field `Z` whose spatial Jacobian is symmetric
(`∂ᵢ Z_j = ∂ⱼ Z_i`, i.e. `Z` is curl-free — the invariant satisfied by `∇p`, by Clairaut on the
smooth pressure) and any order-`(m+1)` angular Sobolev datum `A` of `Z.field`, the datum is
**longitudinal** at a.e. frequency: `ξᵢ Â_j(ξ) = ξⱼ Â_i(ξ)` a.e., so `Â(ξ) ∈ ℂ ∙ ξ_ℂ` a.e.  This
is exactly the hypothesis `Leray.lerayComplementL2_eq_self_of_longitudinal` consumes to conclude
`(I−P)` **fixes** the field (SL5 of P2, `eq:Rpressure`).

This module mirrors lane 079 (`Transverse.lean`) exactly, with the antisymmetric curl pair
`(∂ᵢ Z)_j − (∂ⱼ Z)_i` in place of the divergence sum `∑ⱼ (∂ⱼ Z)_j`.  As in 079, the analytic heart
(`longitudinal_symm_of_curl_free`, the cycles convention) and the dilation transport
(`longitudinal_of_curl_free`, the angular convention) are split into two theorems, so each stays
within the elaboration budget.

## Route (see `research/D01/ATTEMPTS_LONGITUDINAL.md`)

* For fixed `i j`: the scalar field `x ↦ (∂ᵢ Z x)_j − (∂ⱼ Z x)_i` is identically `0`
  (`hcurl`), so the order-`m` datum `(D_i A)_j − (D_j A)_i` realizes the zero distribution;
  by injectivity of `angularRealization m` it is `0` in `L²` (`isSobolevDatum_partialDeriv`
  componentwise, `DerivativeDatum.lean`).
* Peel the outer `cyclesToAngular m` equivalence (injective) and read off the a.e. coefficient
  exactly as 079 does: the common nonzero factor `2πi (1+‖ξ‖²)^{-1/2} W_{-(m+1)}(ξ)` cancels,
  giving `ξᵢ (angularFrequencyDilation.symm (A j)) ξ = ξⱼ (angularFrequencyDilation.symm (A i)) ξ`.
* Transport the dilation-conjugated statement by `ξ ↦ c⁻¹ξ` and apply `angularFrequencyDilation_coeFn`
  (lane 079's helper) to upgrade to the angular convention `ξᵢ Â_j(ξ) = ξⱼ Â_i(ξ)`.
* Combine over the finitely many `(i,j)` pairs with `ae_all_iff`.

Lemma B (`mem_span_r3FreqVec_of_curl_free`) is the pure fibre fact: at `ξ ≠ 0`, the cross
relations `ξᵢ vⱼ = ξⱼ vᵢ` force `v ∈ ℂ ∙ ξ_ℂ`.  Lemma C (`lerayComplement_eq_self_of_longitudinal`)
is the datum-level fixed point, mirroring `lerayComplement_eq_zero_of_transverse`
(`LerayDatum.lean`): it feeds the a.e. line membership (fibre fact + `ξ ≠ 0` null set inline) to
`Leray.lerayComplementL2_eq_self_of_longitudinal` through `lerayComplement_coe`.
`lerayComplement_eq_self_of_curl_free` combines Lemma A and Lemma C for SL8.

No `sorry`, no `axiom`; `#print axioms` is standard (`research/D01/axioms_longitudinal.lean`).
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

/-! ## 1. The cycles-convention longitudinal form -/

/-- **Cycles-convention longitudinality.**  With `A` the order-`(m+1)` angular datum of a curl-free
`Z`, the pre-dilation (cycles-convention) datum is longitudinal a.e.:
`ξᵢ (D⁻¹ A_j) ξ = ξⱼ (D⁻¹ A_i) ξ` for all `i j`.  This is the full analytic content of SL5;
`longitudinal_of_curl_free` transports it to the angular convention. -/
theorem longitudinal_symm_of_curl_free {Z : SmoothL2Field Space}
    (hcurl : ∀ (i j : Fin 3) (x : Space), partialDeriv i Z.field x j = partialDeriv j Z.field x i)
    (m : ℕ) {A : RealVectorSobolev ((m : ℝ) + 1)}
    (hA : IsSobolevDatum ((m : ℝ) + 1) Z.field A) :
    ∀ᵐ ξ : Space ∂volume, ∀ i j : Fin 3,
      ((ξ i : ℝ) : ℂ) * (angularFrequencyDilation.symm (A j : FourierData)) ξ
        = ((ξ j : ℝ) : ℂ) * (angularFrequencyDilation.symm (A i : FourierData)) ξ := by
  set g : Fin 3 → FourierData := fun k => angularFrequencyDilation.symm (A k : FourierData) with hg
  -- The pointwise identification of the directional-derivative component with `∂ₐ Z_k`.
  have hXfield : ∀ (a k : Fin 3) (x : Space),
      ((componentField k Z).directionalField (coordinateVector a)).field x
        = ((partialDeriv a Z.field x k : ℝ) : ℂ) := by
    intro a k x
    rw [← componentField_directionalField]
    simp only [componentField_field, EulerLpTranslation.SmoothL2Field.directionalField_field]
    rfl
  -- The realization of the mixed directional-derivative datum.
  have hreal_mixed : ∀ (a k : Fin 3),
      angularRealization (m : ℝ)
          (angularDirectionalDerivative ((m : ℝ) + 1) (coordinateVector a) (A k : FourierData))
        = physicalDistribution ((componentField k Z).directionalField (coordinateVector a)) := by
    intro a k
    ext ψ
    have hcoe : angularDirectionalDerivative ((m : ℝ) + 1) (coordinateVector a) (A k : FourierData)
        = ((WithLp.toLp 2 fun l =>
            angularDirectionalDerivativeReal ((m : ℝ) + 1) (coordinateVector a) (A l)) k :
              RealSobolevHilbert (m : ℝ)) :=
      (angularDirectionalDerivativeReal_coe ((m : ℝ) + 1) (coordinateVector a) (A k)).symm
    rw [hcoe, (isSobolevDatum_partialDeriv a m hA) k ψ, physicalDistribution_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [hXfield, smul_eq_mul]
  -- The per-pair cycles-convention identity (analytic heart).
  have symm_pair : ∀ (i j : Fin 3), ∀ᵐ ξ : Space ∂volume,
      ((ξ i : ℝ) : ℂ) * (g j) ξ = ((ξ j : ℝ) : ℂ) * (g i) ξ := by
    intro i j
    -- Step 1: the antisymmetric curl combination realizes the zero distribution.
    have hsub0 : angularDirectionalDerivative ((m : ℝ) + 1) (coordinateVector i) (A j : FourierData)
        - angularDirectionalDerivative ((m : ℝ) + 1) (coordinateVector j) (A i : FourierData) = 0 := by
      apply (angularRealization_injective (m : ℝ))
      rw [map_sub, map_zero, hreal_mixed i j, hreal_mixed j i, sub_eq_zero]
      ext ψ
      rw [physicalDistribution_apply, physicalDistribution_apply]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      simp only [hXfield, smul_eq_mul, hcurl i j x]
    -- Step 2: peel the outer angular equivalence (injective).
    have hpeel : sobolevDirectionalDerivative ((m : ℝ) + 1) (coordinateVector i)
          (angularWeightEquiv (-((m : ℝ) + 1)) (g j))
        - sobolevDirectionalDerivative ((m : ℝ) + 1) (coordinateVector j)
          (angularWeightEquiv (-((m : ℝ) + 1)) (g i)) = 0 := by
      apply (cyclesToAngular ((m : ℝ) + 1 - 1)).injective
      rw [map_zero, map_sub]
      exact hsub0
    -- Step 3: read off the a.e. coefficient and cancel the common nonzero factor.
    have hz : ⇑(sobolevDirectionalDerivative ((m : ℝ) + 1) (coordinateVector i)
            (angularWeightEquiv (-((m : ℝ) + 1)) (g j))
          - sobolevDirectionalDerivative ((m : ℝ) + 1) (coordinateVector j)
            (angularWeightEquiv (-((m : ℝ) + 1)) (g i))) =ᵐ[volume] 0 := by
      rw [hpeel]; exact Lp.coeFn_zero ℂ 2 volume
    filter_upwards [hz,
      Lp.coeFn_sub (sobolevDirectionalDerivative ((m : ℝ) + 1) (coordinateVector i)
          (angularWeightEquiv (-((m : ℝ) + 1)) (g j)))
        (sobolevDirectionalDerivative ((m : ℝ) + 1) (coordinateVector j)
          (angularWeightEquiv (-((m : ℝ) + 1)) (g i))),
      sobolevDirectionalDerivative_coeFn ((m : ℝ) + 1) (coordinateVector i)
        (angularWeightEquiv (-((m : ℝ) + 1)) (g j)),
      sobolevDirectionalDerivative_coeFn ((m : ℝ) + 1) (coordinateVector j)
        (angularWeightEquiv (-((m : ℝ) + 1)) (g i)),
      angularWeightEquiv_coeFn (-((m : ℝ) + 1)) (g j),
      angularWeightEquiv_coeFn (-((m : ℝ) + 1)) (g i)] with ξ hz0 hsub hd_i hd_j hw_j hw_i
    have hkey : sobolevDirectionalSymbol (coordinateVector i) ξ
          * (angularWeightSymbol (-((m : ℝ) + 1)) ξ * (g j) ξ)
        - sobolevDirectionalSymbol (coordinateVector j) ξ
          * (angularWeightSymbol (-((m : ℝ) + 1)) ξ * (g i) ξ) = 0 := by
      have hh := hz0
      rw [hsub, Pi.sub_apply, hd_i, hd_j, hw_j, hw_i] at hh
      simpa using hh
    have hσ : ∀ a : Fin 3, sobolevDirectionalSymbol (coordinateVector a) ξ
        = (2 * (Real.pi : ℂ) * Complex.I) * (((ξ a : ℝ) : ℂ) * sobolevBesselWeight (-1) ξ) := by
      intro a
      rw [sobolevDirectionalSymbol]
      congr 3
      rw [coordinateVector, EuclideanSpace.inner_single_right]; simp
    have hW : sobolevBesselWeight (-1) ξ ≠ 0 := by
      simp only [sobolevBesselWeight]; rw [Complex.ofReal_ne_zero]; positivity
    have hAW : angularWeightSymbol (-((m : ℝ) + 1)) ξ ≠ 0 := by
      simp only [angularWeightSymbol, sobolevBesselWeight]
      rw [mul_ne_zero_iff]; constructor <;> · rw [Complex.ofReal_ne_zero]; positivity
    rw [hσ i, hσ j] at hkey
    set C : ℂ := (2 * (Real.pi : ℂ) * Complex.I) * sobolevBesselWeight (-1) ξ
        * angularWeightSymbol (-((m : ℝ) + 1)) ξ with hC
    have hCne : C ≠ 0 := by
      rw [hC]
      refine mul_ne_zero (mul_ne_zero ?_ hW) hAW
      simp [Complex.I_ne_zero, Real.pi_ne_zero]
    have hfactor : C * (((ξ i : ℝ) : ℂ) * (g j) ξ - ((ξ j : ℝ) : ℂ) * (g i) ξ) = 0 := by
      rw [hC]; ring_nf; ring_nf at hkey; linear_combination hkey
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left hCne)
  -- Combine over the finitely many `(i, j)` pairs.
  refine ae_all_iff.2 (fun i => ?_)
  refine ae_all_iff.2 (fun j => ?_)
  exact symm_pair i j

/-! ## 2. The angular-convention longitudinal form (the SL5 deliverable) -/

/-- **Fourier longitudinal form (SL5).**  A curl-free (symmetric-Jacobian) smooth square-integrable
field has a.e. longitudinal Fourier data at every order: `ξᵢ Â_j(ξ) = ξⱼ Â_i(ξ)` a.e., where `A` is
any order-`(m+1)` angular Sobolev datum of `Z.field`.  Fed to
`Leray.lerayComplement_eq_self_of_longitudinal` (via the line-membership fibre fact), this shows
`(I−P)` fixes the field (P2, `eq:Rpressure`). -/
theorem longitudinal_of_curl_free {Z : SmoothL2Field Space}
    (hcurl : ∀ (i j : Fin 3) (x : Space), partialDeriv i Z.field x j = partialDeriv j Z.field x i)
    (m : ℕ) {A : RealVectorSobolev ((m : ℝ) + 1)}
    (hA : IsSobolevDatum ((m : ℝ) + 1) Z.field A) :
    ∀ᵐ ξ : Space ∂volume, ∀ i j : Fin 3,
      ((ξ i : ℝ) : ℂ) * ((A j : FourierData) ξ) = ((ξ j : ℝ) : ℂ) * ((A i : FourierData) ξ) := by
  have hc0 : (0 : ℝ) < frequencyUnit := frequencyUnit_pos
  have hstar := longitudinal_symm_of_curl_free hcurl m hA
  set κ : ℝ≥0∞ := ENNReal.ofReal (|(frequencyUnit⁻¹ ^ (Module.finrank ℝ Space))⁻¹|) with hκ
  have hMP : MeasurePreserving (fun ξ : Space => frequencyUnit⁻¹ • ξ) volume (κ • volume) :=
    ⟨(continuous_const_smul _).measurable, Measure.map_addHaar_smul volume (inv_ne_zero hc0.ne')⟩
  have hfwd : ∀ k : Fin 3, ∀ᵐ ξ : Space ∂volume,
      ((A k : FourierData) ξ) = (frequencyUnit ^ (-3/2 : ℝ) : ℝ) •
        (angularFrequencyDilation.symm (A k : FourierData)) (frequencyUnit⁻¹ • ξ) := by
    intro k
    have h1 := angularFrequencyDilation_coeFn (angularFrequencyDilation.symm (A k : FourierData))
    rw [LinearIsometryEquiv.apply_symm_apply] at h1
    exact h1
  refine ae_all_iff.2 (fun i => ?_)
  refine ae_all_iff.2 (fun j => ?_)
  have hpair : ∀ᵐ ξ : Space ∂volume,
      ((ξ i : ℝ) : ℂ) * (angularFrequencyDilation.symm (A j : FourierData)) ξ
        = ((ξ j : ℝ) : ℂ) * (angularFrequencyDilation.symm (A i : FourierData)) ξ := by
    filter_upwards [hstar] with ξ hξ; exact hξ i j
  have htrans : ∀ᵐ ξ : Space ∂volume,
      (((frequencyUnit⁻¹ • ξ) i : ℝ) : ℂ)
          * (angularFrequencyDilation.symm (A j : FourierData)) (frequencyUnit⁻¹ • ξ)
        = (((frequencyUnit⁻¹ • ξ) j : ℝ) : ℂ)
          * (angularFrequencyDilation.symm (A i : FourierData)) (frequencyUnit⁻¹ • ξ) :=
    hMP.quasiMeasurePreserving.ae (Measure.ae_smul_measure hpair κ)
  filter_upwards [htrans, hfwd i, hfwd j] with ξ ht hi hj
  have hsmul : ∀ k : Fin 3, ((frequencyUnit⁻¹ • ξ) k : ℝ) = frequencyUnit⁻¹ * ξ k := fun k => rfl
  rw [hi, hj]
  simp only [hsmul, Complex.ofReal_mul, Complex.real_smul] at ht ⊢
  have hcinv : ((frequencyUnit⁻¹ : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact inv_ne_zero hc0.ne'
  have hgs : ((ξ i : ℝ) : ℂ) * (angularFrequencyDilation.symm (A j : FourierData)) (frequencyUnit⁻¹ • ξ)
      = ((ξ j : ℝ) : ℂ) * (angularFrequencyDilation.symm (A i : FourierData)) (frequencyUnit⁻¹ • ξ) := by
    have hh : ((frequencyUnit⁻¹ : ℝ) : ℂ)
        * (((ξ i : ℝ) : ℂ) * (angularFrequencyDilation.symm (A j : FourierData)) (frequencyUnit⁻¹ • ξ)
          - ((ξ j : ℝ) : ℂ) * (angularFrequencyDilation.symm (A i : FourierData)) (frequencyUnit⁻¹ • ξ)) = 0 := by
      linear_combination ht
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hcinv)
  linear_combination ((frequencyUnit ^ (-3/2 : ℝ) : ℝ) : ℂ) * hgs

end NSFormalization.Section4.D01

/-! ## 3. Lemmas B and C — the frequency-line membership and the datum-level fixed point -/

namespace NSFormalization.Section4.D01.Leray

open MeasureTheory
open scoped ComplexConjugate
open NSFormalization.Source.FiniteHilbertBochner (assemble coordinates)
open NSFormalization.Source.RealSobolev (RealSobolevHilbert FourierData)
open NSFormalization.Paper3 (RealVectorSobolev)

/-- **Lemma B — a.e. membership in the frequency line (fibre fact).**  At a nonzero frequency `ξ`,
a complex fibre vector `v` whose components satisfy the curl relations `ξᵢ vⱼ = ξⱼ vᵢ` lies on the
complex frequency line `ℂ ∙ ξ_ℂ`.  (Take a coordinate `k` with `ξ k ≠ 0`; then
`v = (v k / ξ k) • ξ_ℂ`.)  This is the fibre content behind the codomain of the SL5 fixed point. -/
theorem mem_span_r3FreqVec_of_curl_free (ξ : MNS2.R3) (hξ : ξ ≠ 0) (v : MNS2.R3C)
    (hv : ∀ i j : Fin 3, ((ξ i : ℝ) : ℂ) * v j = ((ξ j : ℝ) : ℂ) * v i) :
    v ∈ ℂ ∙ MNS2.r3FrequencyVectorComplex ξ := by
  obtain ⟨k, hk⟩ : ∃ k : Fin 3, ξ k ≠ 0 := by
    by_contra hcon
    exact hξ (by ext k; simpa using not_exists.mp hcon k)
  have hkc : ((ξ k : ℝ) : ℂ) ≠ 0 := by rw [Complex.ofReal_ne_zero]; exact hk
  rw [Submodule.mem_span_singleton]
  refine ⟨v k / ((ξ k : ℝ) : ℂ), ?_⟩
  apply PiLp.ext
  intro j
  rw [PiLp.smul_apply, smul_eq_mul]
  have hfr : (MNS2.r3FrequencyVectorComplex ξ) j = ((ξ j : ℝ) : ℂ) := rfl
  rw [hfr, div_mul_eq_mul_div, div_eq_iff hkc]
  linear_combination - hv k j

/-- **Lemma C — the datum-level fixed point (SL5).**  If the datum components are a.e. longitudinal
in the lane-089 curl shape `ξᵢ Â_j(ξ) = ξⱼ Â_i(ξ)`, the datum-carrier Leray-complement multiplier
fixes the datum.  Mirrors `lerayComplement_eq_zero_of_transverse`: the a.e. line membership
(Lemma B + the `ξ ≠ 0` null set, inline) feeds `lerayComplementL2_eq_self_of_longitudinal`. -/
theorem lerayComplement_eq_self_of_longitudinal (s : ℝ) (h : RealVectorSobolev s)
    (hlong : ∀ᵐ ξ ∂(volume : Measure MNS2.R3), ∀ i j : Fin 3,
      ((ξ i : ℝ) : ℂ) * (((h j : FourierData)) ξ) = ((ξ j : ℝ) : ℂ) * (((h i : FourierData)) ξ)) :
    lerayComplement s h = h := by
  set b := assemble 2 volume (fun j => ((h j : FourierData))) with hb
  have hb0 : lerayComplementL2 b = b := by
    apply lerayComplementL2_eq_self_of_longitudinal
    have hne : ∀ᵐ ξ ∂(volume : Measure MNS2.R3), ξ ≠ 0 := by simp [ae_iff]
    have hall : ∀ᵐ ξ ∂(volume : Measure MNS2.R3), ∀ j : Fin 3,
        (((h j : FourierData)) : MNS2.R3 → ℂ) ξ = (b ξ) j := by
      rw [ae_all_iff]; intro j
      rw [hb, ← coordinates_assemble volume (fun j => ((h j : FourierData))) j]
      exact coordinates_ae volume b j
    filter_upwards [hlong, hall, hne] with ξ hξ hall hne
    apply mem_span_r3FreqVec_of_curl_free ξ hne
    intro p q
    rw [← hall p, ← hall q]
    exact hξ p q
  apply PiLp.ext; intro i; apply Subtype.ext
  rw [lerayComplement_coe, hb0, hb, coordinates_assemble]

/-- **The SL5 deliverable, assembled.**  For a curl-free (symmetric-Jacobian) smooth
square-integrable field `Z` and any order-`(m+1)` datum `A` of `Z.field`, the datum-carrier
Leray-complement multiplier fixes `A`: `(I−P) A = A`.  Combines Lemma A
(`longitudinal_of_curl_free`) with Lemma C. -/
theorem lerayComplement_eq_self_of_curl_free {Z : EulerLpTranslation.SmoothL2Field Space}
    (hcurl : ∀ (i j : Fin 3) (x : Space), partialDeriv i Z.field x j = partialDeriv j Z.field x i)
    (m : ℕ) {A : RealVectorSobolev ((m : ℝ) + 1)}
    (hA : IsSobolevDatum ((m : ℝ) + 1) Z.field A) :
    lerayComplement ((m : ℝ) + 1) A = A :=
  lerayComplement_eq_self_of_longitudinal ((m : ℝ) + 1) A (longitudinal_of_curl_free hcurl m hA)

end NSFormalization.Section4.D01.Leray
