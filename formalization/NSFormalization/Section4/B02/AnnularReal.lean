import NSFormalization.Section4.B02.AnnularSchwartz
import NSFormalization.Section4.B02.Cutoff
import NSFormalization.Section4.B02.LebesgueDatum

/-!
# B02 unit 2: reality and the slice/integrability rows of `annularSchwartz`

This module supplies three of the remaining sub-lemmas of the spec field
`annularSchwartz` (`research/B02/Spec.lean:362-364`), the single remaining
hypothesis of `Section4/B02/Cutoff.lean`'s `spatialApproxHomogeneous_of`.  See
`research/B02/U2_SPLIT.md` for the full table; lane 078 proved **SL1**
(`contDiff_rpow_mul_of_annulus`) and **SL2** (`exists_schwartz_angularFourier_eq`)
in `AnnularSchwartz`.  Here we prove:

* **SL3** (reality) `angularFourier_realPart_ae`: the manuscript step
  `paper/sections/04-whole-space.tex:249` ("real parts").  If `φ` is a Schwartz
  function realizing the homogeneous weight `Gᵢ ξ = ((‖ξ‖ ^ (-s) : ℝ) : ℂ) · g ξ`
  of a real datum component (`angularFourier ↑φ = Gᵢ` pointwise, from SL2), then
  the *real part* `postcompCLM ofRealCLM (postcompCLM reCLM φ)` still has angular
  Fourier transform `=ᵐ Gᵢ`.  The proof uses the conjugate-reflection symmetry of
  `angularFourier` (`angularFourier_conj`, from `fourier_conjugate`) together with
  the reality (conjugate-reflection) symmetry of the datum `W` in the sense of
  `Source.RealSobolev` (via `Annular.realSobolevHilbert_conj_reflection_ae`).  Only an a.e. identity
  is proved — that is all the integral identity in SL4c needs.
* **SL4a** (slice) `isSliceDistribution_schwartzVector`: the complexified real
  Schwartz vector realizes the datum's slice distribution.
* **SL4b** (integrability) `integrable_weight_annular`: the homogeneous pairing of
  the weighted datum with a Schwartz test is integrable.

The reality/assembly rows SL4c and the final `annularSchwartz` assembly are the
next lane.
-/

noncomputable section

namespace NSFormalization.Section4.B02

open MeasureTheory
open NSFormalization.Paper3
open NSFormalization.Source (angularFourier)
open NSFormalization.Source.RealSobolev
open NavierStokes.ProblemStatement (Space)
open scoped ContDiff ComplexConjugate SchwartzMap ENNReal

/-! ## Linearity and conjugation of the angular Fourier transform on Schwartz data -/

/-- Moved to `Paper3/AngularFourierDilation.lean` in lane 109; alias kept for downstream.

The angular Fourier transform intertwines physical conjugation with conjugate reflection:
`angularFourier (conj f) ξ = conj (angularFourier f (-ξ))`. -/
alias angularFourier_conj := NSFormalization.Paper3.angularFourier_conj

/-- The angular Fourier transform is additive on Schwartz data (routed through the
Schwartz-level CLM `schwartzAngularDilation`, so no integrability side condition is
needed). -/
theorem angularFourier_schwartz_add (φ ψ : SchwartzMap Space ℂ) (ξ : Space) :
    angularFourier (↑(φ + ψ)) ξ = angularFourier (↑φ) ξ + angularFourier (↑ψ) ξ := by
  simp only [← schwartzAngularDilation_fourier_apply, schwartzAngularDilation_apply,
    FourierTransform.fourier_add, add_apply, smul_add]

/-- The angular Fourier transform is `ℝ`-homogeneous on Schwartz data. -/
theorem angularFourier_schwartz_smul (r : ℝ) (φ : SchwartzMap Space ℂ) (ξ : Space) :
    angularFourier (↑(r • φ)) ξ = r • angularFourier (↑φ) ξ := by
  simp only [← schwartzAngularDilation_fourier_apply, schwartzAngularDilation_apply,
    FourierTransform.fourier_smul, smul_apply]
  rw [smul_comm]

/-- The complexified real part `postcompCLM ofRealCLM (postcompCLM reCLM φ)` is the
half-sum `½(φ + conj φ)` at the Schwartz level (`realPartSchwartz`, `RealSobolev.lean:84`). -/
theorem postcompReCLM_ofReal_eq (φ : SchwartzMap Space ℂ) :
    SchwartzMap.postcompCLM Complex.ofRealCLM (SchwartzMap.postcompCLM Complex.reCLM φ)
      = (1 / 2 : ℝ) • (φ + conjugateSchwartz φ) := by
  apply SchwartzMap.ext
  intro x
  rw [SchwartzMap.postcompCLM_apply, SchwartzMap.postcompCLM_apply, Complex.reCLM_apply,
    Complex.ofRealCLM_apply]
  exact (realPartSchwartz_apply φ x).symm

/-- The pointwise real-part identity for the angular Fourier transform:
`angularFourier ↑(re-part φ) ξ = ½ (angularFourier ↑φ ξ + conj (angularFourier ↑φ (-ξ)))`. -/
theorem angularFourier_realPart_apply (φ : SchwartzMap Space ℂ) (ξ : Space) :
    angularFourier (↑(SchwartzMap.postcompCLM Complex.ofRealCLM
        (SchwartzMap.postcompCLM Complex.reCLM φ))) ξ
      = (1 / 2 : ℝ) • (angularFourier (↑φ) ξ + conj (angularFourier (↑φ) (-ξ))) := by
  rw [postcompReCLM_ofReal_eq, angularFourier_schwartz_smul, angularFourier_schwartz_add,
    show (↑(conjugateSchwartz φ) : Space → ℂ) = fun x => conj ((φ : Space → ℂ) x) from
      funext (fun x => conjugateSchwartz_apply φ x), angularFourier_conj]

/-! ## SL3.  Reality of the realized homogeneous weight -/

/-- `research/B02/U2_SPLIT.md` SL3, `04-whole-space.tex:249`.  Let `W` be a real
datum, `g` a representative of its `i`-th Fourier component, and `φ` a Schwartz map
whose angular Fourier transform is the homogeneous weight
`Gᵢ ξ = ((‖ξ‖ ^ (-s) : ℝ) : ℂ) · g ξ` (SL2 output).  Then the complexified real
part of `φ` has angular Fourier transform `=ᵐ Gᵢ`.  The equality is only a.e.,
which is exactly what SL4c's integral identity consumes; we do **not** upgrade to
reality of `φ` itself. -/
theorem angularFourier_realPart_ae {s : ℝ} (W : RealVectorSobolev s) (i : Fin 3)
    {g : Space → ℂ} (hae : ((W i : FourierData) : Space → ℂ) =ᵐ[volume] g)
    {φ : SchwartzMap Space ℂ}
    (hφ : ∀ ξ : Space, angularFourier (↑φ) ξ = ((‖ξ‖ ^ (-s) : ℝ) : ℂ) * g ξ) :
    angularFourier (↑(SchwartzMap.postcompCLM Complex.ofRealCLM
        (SchwartzMap.postcompCLM Complex.reCLM φ)))
      =ᵐ[volume] fun ξ => ((‖ξ‖ ^ (-s) : ℝ) : ℂ) * g ξ := by
  -- Reality of the datum component (shared helper `realSobolevHilbert_conj_reflection_ae`).
  have hSym := realSobolevHilbert_conj_reflection_ae (W i)
  have hWaeneg := (Measure.measurePreserving_neg
    (volume : Measure Space)).quasiMeasurePreserving.ae hae
  -- Conjugate-reflection symmetry of the representative `g`.
  have hgconj : ∀ᵐ ξ ∂volume, conj (g (-ξ)) = g ξ := by
    filter_upwards [hSym, hae, hWaeneg] with ξ e1 e2 e3
    rw [← e3, ← e1]; exact e2
  -- ... hence of the weighted angular transform (real weight, `‖-ξ‖ = ‖ξ‖`).
  have hφreal : ∀ᵐ ξ ∂volume, conj (angularFourier (↑φ) (-ξ)) = angularFourier (↑φ) ξ := by
    filter_upwards [hgconj] with ξ hξ
    rw [hφ (-ξ), hφ ξ, map_mul, Complex.conj_ofReal, norm_neg, hξ]
  -- Combine the pointwise real-part identity with a.e. Hermitian symmetry.
  filter_upwards [hφreal] with ξ hξ
  rw [angularFourier_realPart_apply, hξ, hφ ξ, Complex.real_smul]
  push_cast
  ring

/-! ## SL4a.  The complexified real Schwartz vector realizes the slice distribution -/

/-- `research/B02/U2_SPLIT.md` SL4a.  For a real Schwartz vector `ψ`, the family of
tempered distributions `U i = ↑(postcompCLM ofRealCLM (ψ i))` is exactly the slice
distribution of the vector field `schwartzVector ψ`. -/
theorem isSliceDistribution_schwartzVector (ψ : Fin 3 → SchwartzMap Space ℝ) :
    IsSliceDistribution (schwartzVector ψ)
      (fun i => ((SchwartzMap.postcompCLM Complex.ofRealCLM (ψ i) :
        SchwartzMap Space ℂ) : 𝓢'(Space, ℂ))) := by
  intro i χ
  show ((SchwartzMap.postcompCLM Complex.ofRealCLM (ψ i) : SchwartzMap Space ℂ) :
      𝓢'(Space, ℂ)) χ = ∫ x : Space, χ x * ((schwartzVector ψ x i : ℝ) : ℂ)
  rw [SchwartzMap.coe_apply]
  simp only [SchwartzMap.postcompCLM_apply, Complex.ofRealCLM_apply, smul_eq_mul,
    schwartzVector_apply]

/-! ## SL4b.  Integrability of the homogeneous pairing -/

/-- `research/B02/U2_SPLIT.md` SL4b.  The homogeneous pairing
`ξ ↦ φ ξ · (‖ξ‖ ^ (-s) · (W i) ξ)` of a Schwartz test with the weighted datum is
integrable: a.e. it equals `φ ξ · Gᵢ ξ`, and `Gᵢ` (SL1) is continuous with compact
support, so its product with the continuous `φ` has compact support and is
integrable. -/
theorem integrable_weight_annular {s δ R : ℝ} (hδ : 0 < δ) (W : RealVectorSobolev s)
    (i : Fin 3) {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hsupp : tsupport g ⊆ closedFrequencyAnnulus δ R)
    (hae : ((W i : FourierData) : Space → ℂ) =ᵐ[volume] g) (φ : SchwartzMap Space ℂ) :
    Integrable (fun ξ : Space => (φ : Space → ℂ) ξ *
        (((‖ξ‖ ^ (-s) : ℝ) : ℂ) * ((W i : FourierData) : Space → ℂ) ξ)) volume := by
  obtain ⟨hGsmooth, hGcs⟩ := contDiff_rpow_mul_of_annulus (s := s) hδ hg hsupp
  have hint : Integrable (fun ξ : Space => (φ : Space → ℂ) ξ *
      (((‖ξ‖ ^ (-s) : ℝ) : ℂ) * g ξ)) volume := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact φ.continuous.mul hGsmooth.continuous
    · show HasCompactSupport ((⇑φ) * fun ξ : Space => ((‖ξ‖ ^ (-s) : ℝ) : ℂ) * g ξ)
      exact hGcs.mul_left
  refine hint.congr ?_
  filter_upwards [hae] with ξ hξ
  rw [hξ]

/-! ## SL4c.  The homogeneous pairing identity -/

/-- `research/B02/U2_SPLIT.md` SL4c (route verified by the lane-084 reviewer in
`/tmp/084_review_sl4c.lean`).  The distributional pairing of the complexified real
part of `φ` with a Schwartz test `χ` equals the weighted physical integral against
`(W i)`.  Stated with the exact three-layer coercion of the
`angularFourierDistribution …` conjunct of `IsHomogeneousDatum` (`Cutoff.lean:246`).
Only the a.e. identity SL3 is used (`integral_congr_ae`); no integrability input is
needed here (SL4b feeds the *other* conjunct of `IsHomogeneousDatum`). -/
theorem angularFourierDistribution_realPart_pairing {s : ℝ} (W : RealVectorSobolev s)
    (i : Fin 3) {g : Space → ℂ} (hae : ((W i : FourierData) : Space → ℂ) =ᵐ[volume] g)
    {φ : SchwartzMap Space ℂ}
    (hφ : ∀ ξ : Space, angularFourier (↑φ) ξ = ((‖ξ‖ ^ (-s) : ℝ) : ℂ) * g ξ)
    (χ : SchwartzMap Space ℂ) :
    angularFourierDistribution
        ((SchwartzMap.postcompCLM Complex.ofRealCLM
          (SchwartzMap.postcompCLM Complex.reCLM φ) : SchwartzMap Space ℂ) : 𝓢'(Space, ℂ)) χ
      = ∫ ξ : Space, (χ : Space → ℂ) ξ *
          (((‖ξ‖ ^ (-s) : ℝ) : ℂ) * ((W i : FourierData) : Space → ℂ) ξ) := by
  rw [angularFourierDistribution_schwartz_apply]
  refine integral_congr_ae ?_
  filter_upwards [angularFourier_realPart_ae W i hae hφ, hae] with ξ h1 h2
  rw [smul_eq_mul, h1, h2]

/-! ## SL4.  Assembly: the spec field `annularSchwartz` -/

/-- `research/B02/Spec.lean:362-364` `annularSchwartz`, `04-whole-space.tex:241,249`.
Every smooth annular datum `W` is realized as a real Schwartz vector field
`schwartzVector ψ` whose homogeneous slice datum is `W`.  The witness is the
inverse angular Fourier transform of the homogeneous weight `Gᵢ` (SL1 + SL2), made
real by taking real parts (SL3); its slice distribution is SL4a and each component
is a homogeneous datum by SL4b (integrability) and SL4c (pairing).  The `δ < R`
binder is unused (`0 < δ` alone makes `‖ξ‖^(-s)` smooth on the annulus) but is kept
to match the spec field verbatim.  Assembly verified by the lane-084 reviewer
(`/tmp/084_review_sl4c.lean`). -/
theorem annularSchwartz : ∀ (s : ℝ) (δ R : ℝ), 0 < δ → δ < R →
    ∀ W : RealVectorSobolev s, IsAnnularDatum δ R W →
    ∃ ψ : Fin 3 → SchwartzMap Space ℝ, IsHomogeneousSliceDatum s (schwartzVector ψ) W := by
  intro s δ R hδ _hδR W hW
  obtain ⟨g, hg, hsupp, hae⟩ := hW
  choose φ hφ using fun i : Fin 3 => exists_schwartz_angularFourier_eq
    (contDiff_rpow_mul_of_annulus (s := s) hδ (hg i) (hsupp i)).1
    (contDiff_rpow_mul_of_annulus (s := s) hδ (hg i) (hsupp i)).2
  exact ⟨fun i => SchwartzMap.postcompCLM Complex.reCLM (φ i),
    fun i => ((SchwartzMap.postcompCLM Complex.ofRealCLM
      (SchwartzMap.postcompCLM Complex.reCLM (φ i)) : SchwartzMap Space ℂ) : 𝓢'(Space, ℂ)),
    isSliceDistribution_schwartzVector _, fun i χ =>
      ⟨integrable_weight_annular hδ W i (hg i) (hsupp i) (hae i) χ,
        angularFourierDistribution_realPart_pairing W i (hae i) (hφ i) χ⟩⟩

/-- The fully unconditional stage-4 diagonal density: `spatialApproxHomogeneous_of_units`
(`LebesgueDatum.lean`) with its remaining hypothesis (unit 2, `annularSchwartz`)
discharged.  Compact-smooth real vector fields are dense in `Ḣ^s(ℝ³;ℝ³)` for `s` in
`SplitRange`, measured by the datum norm — no hypotheses.  This is the spec field
`spatialApproxHomogeneous` (`research/B02/Spec.lean:515-518`). -/
theorem spatialApproxHomogeneous :
    ∀ s : ℝ, SplitRange s → ∀ (A : RealVectorSobolev s) (η : ℝ≥0∞), 0 < η →
      ∃ (h : SpatialField) (H : RealVectorSobolev s),
        ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧ IsHomogeneousSliceDatum s h H ∧ ‖H - A‖ₑ < η :=
  spatialApproxHomogeneous_of_units annularSchwartz

end NSFormalization.Section4.B02
