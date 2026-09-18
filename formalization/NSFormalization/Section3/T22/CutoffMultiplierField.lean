import NSFormalization.Section3.T22.CutoffMultiplier
import NSFormalization.Section3.T22.Domain
import Mathlib.Analysis.Fourier.Convolution

/-!
# T22 U-A3b — the verbatim `cutoffMultiplier` field (`03-torus.tex:616-624`)

This module closes `BoundedDomainNormAPI.cutoffMultiplier`
(`Section3/T22/Domain.lean`) on top of the lane-397 analytic engine
`eLpNorm_cutoff_multiplier_le` (`Section3/T22/CutoffMultiplier.lean`).
-/

noncomputable section

namespace NSFormalization.Section3.T22

open MeasureTheory FourierTransform FourierTransformInv NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source (angularFourier frequencyUnit frequencyUnit_pos)
open NSFormalization.Source.RealSobolev
  (FourierData RealSobolevHilbert realSymmetry realSubspace mem_realSubspace_iff conjugateSchwartz
    conjugateSchwartz_apply weightedFourierLp_conjugate)
open NavierStokes.R3ConvolutionYoung (scalarConvolution)
open scoped ContDiff ENNReal SchwartzMap

/-! ## 1. The Schwartz-level product ↔ convolution identity -/

/-- **Fourier transform of a product is the convolution of the transforms.**
Mathlib supplies only the forward direction `𝓕 (f ∗ g) = 𝓕f · 𝓕g`
(`SchwartzMap.fourier_convolution`).  The direction needed here is obtained by
running the Schwartz convolution `SchwartzMap.convolution` on the inverse
transforms and turning `𝓕⁻` into `𝓕` by the reflection
`Real.fourierInv_eq_fourier_neg` and the reflection invariance of the
Lebesgue integral. -/
theorem fourier_mul_eq_scalarConvolution (u v : SchwartzMap Space ℂ) (ξ : Space) :
    𝓕 (fun x => u x * v x) ξ =
      scalarConvolution (𝓕 (u : Space → ℂ)) (𝓕 (v : Space → ℂ)) ξ := by
  set P : SchwartzMap Space ℂ := SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) u v with hP
  have hPco : (P : Space → ℂ) = fun x => u x * v x := by
    funext x; rw [hP, SchwartzMap.pairing_apply_apply]; rfl
  set W : SchwartzMap Space ℂ :=
    SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕⁻ u) (𝓕⁻ v) with hW
  have hFW : 𝓕 W = P := by
    rw [hW, SchwartzMap.fourier_convolution, FourierTransform.fourier_fourierInv_eq,
      FourierTransform.fourier_fourierInv_eq]
  have hWP : W = 𝓕⁻ P := by rw [← hFW, FourierTransform.fourierInv_fourier_eq]
  have hWval : ∀ η : Space,
      W η = ∫ y : Space, (𝓕⁻ (u : Space → ℂ)) y * (𝓕⁻ (v : Space → ℂ)) (η - y) := by
    intro η
    rw [hW, SchwartzMap.convolution_apply]
    simp only [convolution, ContinuousLinearMap.mul_apply']
    simp only [SchwartzMap.fourierInv_coe]
  have hkey := hWval (-ξ)
  rw [hWP, SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, neg_neg, hPco] at hkey
  rw [hkey]
  have hrw : ∀ y : Space, (𝓕⁻ (u : Space → ℂ)) y * (𝓕⁻ (v : Space → ℂ)) (-ξ - y)
      = (fun z : Space => 𝓕 (u : Space → ℂ) z * 𝓕 (v : Space → ℂ) (ξ - z)) (-y) := by
    intro y
    rw [Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq_fourier_neg]
    congr 2
    abel_nf
  rw [integral_congr_ae (Filter.Eventually.of_forall hrw)]
  exact integral_neg_eq_self
    (fun z : Space => 𝓕 (u : Space → ℂ) z * 𝓕 (v : Space → ℂ) (ξ - z)) volume

/-- **Angular normalization of the product ↔ convolution identity.**  In the
manuscript's angular convention `angularFourier f ξ = c^{-3/2} 𝓕f (c⁻¹ξ)`
(`c = frequencyUnit`) the convolution picks up exactly one extra amplitude
factor `c^{-3/2}`, because the `c³` Jacobian of the substitution `y = c z`
cancels only two of the three amplitudes. -/
theorem angularFourier_mul (u v : SchwartzMap Space ℂ) (ξ : Space) :
    angularFourier (fun x => u x * v x) ξ =
      (frequencyUnit ^ (-3 / 2 : ℝ)) •
        scalarConvolution (angularFourier (u : Space → ℂ)) (angularFourier (v : Space → ℂ)) ξ := by
  have hc0 : (0:ℝ) < frequencyUnit := frequencyUnit_pos
  have hfr : Module.finrank ℝ Space = 3 := by simp [Space]
  set d : ℝ := frequencyUnit ^ (-3 / 2 : ℝ) with hd
  have hdd : d * d * frequencyUnit ^ (3 : ℕ) = 1 := by
    rw [hd, ← Real.rpow_add hc0, ← Real.rpow_natCast frequencyUnit 3, ← Real.rpow_add hc0]
    norm_num
  set G : Space → ℂ := fun z : Space =>
    𝓕 (u : Space → ℂ) z * 𝓕 (v : Space → ℂ) (frequencyUnit⁻¹ • ξ - z) with hG
  have hstep : ∀ y : Space,
      angularFourier (u : Space → ℂ) y * angularFourier (v : Space → ℂ) (ξ - y)
        = (d * d) • G (frequencyUnit⁻¹ • y) := by
    intro y
    show (d • 𝓕 (u : Space → ℂ) (frequencyUnit⁻¹ • y)) *
        (d • 𝓕 (v : Space → ℂ) (frequencyUnit⁻¹ • (ξ - y))) = _
    rw [hG, smul_sub]
    simp only [Complex.real_smul, Complex.ofReal_mul]
    ring
  have hconv :
      scalarConvolution (angularFourier (u : Space → ℂ)) (angularFourier (v : Space → ℂ)) ξ
        = scalarConvolution (𝓕 (u : Space → ℂ)) (𝓕 (v : Space → ℂ)) (frequencyUnit⁻¹ • ξ) := by
    show (∫ y : Space, angularFourier (u : Space → ℂ) y *
        angularFourier (v : Space → ℂ) (ξ - y)) = ∫ z : Space, G z
    rw [integral_congr_ae (Filter.Eventually.of_forall hstep)]
    rw [integral_smul, Measure.integral_comp_inv_smul_of_nonneg volume G hc0.le, hfr]
    rw [smul_smul, hdd, one_smul]
  rw [hconv]
  show d • 𝓕 (fun x => u x * v x) (frequencyUnit⁻¹ • ξ) = _
  rw [fourier_mul_eq_scalarConvolution]

/-! ## 2. The angular datum of a Schwartz function -/

/-- The bundled `ℝ`-linear angular datum map of the datum layer. -/
def angularDatumL (s : ℝ) : SchwartzMap Space ℂ →L[ℝ] Lp ℂ 2 (volume : Measure Space) :=
  ((angularFrequencyDilation.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars
      ℝ).comp (angularCoordinateDatum s)

@[simp] theorem angularDatumL_apply (s : ℝ) (φ : SchwartzMap Space ℂ) :
    angularDatumL s φ = angularDatum s φ := rfl

theorem denseRange_angularDatumL (s : ℝ) : DenseRange (angularDatumL s) :=
  (angularFrequencyDilation.surjective.denseRange).comp (denseRange_angularCoordinateDatum s)
    angularFrequencyDilation.continuous

/-- **The a.e. representative of the angular datum.**  It is exactly the
Bessel weight `besselW s` times the angular Fourier transform. -/
theorem angularDatum_ae (s : ℝ) (φ : SchwartzMap Space ℂ) :
    (angularDatum s φ : Space → ℂ) =ᵐ[volume]
      fun ξ => (besselW s ξ : ℝ) • angularFourier (φ : Space → ℂ) ξ := by
  have hc0 : (0:ℝ) < frequencyUnit := frequencyUnit_pos
  set κ : ℝ≥0∞ := ENNReal.ofReal (|(frequencyUnit⁻¹ ^ (Module.finrank ℝ Space))⁻¹|) with hκ
  have hMP : MeasurePreserving (fun ξ : Space => frequencyUnit⁻¹ • ξ) volume (κ • volume) :=
    ⟨(continuous_const_smul _).measurable, Measure.map_addHaar_smul volume (inv_ne_zero hc0.ne')⟩
  have hpush := hMP.quasiMeasurePreserving.ae
    (Measure.ae_smul_measure (angularCoordinateDatum_ae s φ) κ)
  filter_upwards [angularFrequencyDilation_coeFn (angularCoordinateDatum s φ), hpush] with ξ h1 h2
  rw [show (angularDatum s φ : Space → ℂ) ξ
      = ((angularFrequencyDilation (angularCoordinateDatum s φ) : Space → ℂ)) ξ from rfl, h1, h2]
  rw [smul_inv_smul₀ hc0.ne', SchwartzMap.fourier_coe]
  unfold angularFourier besselW sobolevBesselWeight
  simp only [Complex.real_smul]
  ring

/-! ## 3. The multiplier bound on the Schwartz core -/

/-- The `U-A3b` field constant: the lane-397 operator constant
`cutoffMultiplierConst s χ` rescaled by the angular amplitude
`frequencyUnit^{-3/2}` and shifted by `1`, so that it is **positive for every**
`χ` (including `χ = 0`, where the operator constant vanishes). -/
def cutoffFieldConst (s : ℝ) (χ : Space → ℝ) : ℝ :=
  frequencyUnit ^ (-3 / 2 : ℝ) * cutoffMultiplierConst s χ + 1

theorem cutoffFieldConst_pos (s : ℝ) (χ : Space → ℝ) : 0 < cutoffFieldConst s χ := by
  have h : 0 ≤ frequencyUnit ^ (-3 / 2 : ℝ) * cutoffMultiplierConst s χ :=
    mul_nonneg (Real.rpow_nonneg frequencyUnit_pos.le _) (cutoffMultiplierConst_nonneg s χ)
  unfold cutoffFieldConst; linarith

/-- The cutoff, complexified, has temperate growth (it is Schwartz). -/
theorem cutoff_hasTemperateGrowth {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) : (fun x : Space => (χ x : ℂ)).HasTemperateGrowth :=
  (cutoffSchwartz hχ hc).hasTemperateGrowth

/-- **The multiplier bound on the Schwartz core.**  Multiplication by the
cutoff `χ` is bounded on the angular data of Schwartz functions, with constant
`cutoffFieldConst s χ`.  Route: `angularDatum_ae` turns both sides into
Bessel-weighted angular transforms, `angularFourier_mul` turns the product into
a convolution, and `eLpNorm_cutoff_multiplier_le` (lane 397) is the estimate. -/
theorem norm_angularDatum_smulLeft_le {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (s : ℝ) (φ : SchwartzMap Space ℂ) :
    ‖angularDatum s (SchwartzMap.smulLeftCLM ℂ (fun x => (χ x : ℂ)) φ)‖
      ≤ cutoffFieldConst s χ * ‖angularDatum s φ‖ := by
  classical
  set d : ℝ := frequencyUnit ^ (-3 / 2 : ℝ) with hdd
  have hd0 : 0 ≤ d := Real.rpow_nonneg frequencyUnit_pos.le _
  set K : Space → ℂ := angularFourier (fun x => (χ x : ℂ)) with hK
  set g : Space → ℂ := angularFourier (φ : Space → ℂ) with hg
  set X : SchwartzMap Space ℂ := cutoffSchwartz hχ hc with hX
  -- the weighted profile of the input datum is in `L²`
  have hmem : MemLp (fun η : Space => (besselW s η : ℝ) • g η) 2 volume :=
    (memLp_congr_ae (angularDatum_ae s φ)).mp (Lp.memLp (angularDatum s φ))
  have hinput : eLpNorm (fun η : Space => (besselW s η : ℝ) • g η) 2 volume
      = eLpNorm (angularDatum s φ : Space → ℂ) 2 volume :=
    (eLpNorm_congr_ae (angularDatum_ae s φ)).symm
  -- the output datum is the weighted convolution, up to the amplitude `d`
  have hprod : ((SchwartzMap.smulLeftCLM ℂ (fun x => (χ x : ℂ)) φ : SchwartzMap Space ℂ) :
      Space → ℂ) = fun x => X x * φ x := by
    funext x
    rw [SchwartzMap.smulLeftCLM_apply_apply (cutoff_hasTemperateGrowth hχ hc)]
    rw [hX, cutoffSchwartz_apply, smul_eq_mul]
  have hout : (angularDatum s (SchwartzMap.smulLeftCLM ℂ (fun x => (χ x : ℂ)) φ) : Space → ℂ)
      =ᵐ[volume] fun ξ => d • ((besselW s ξ : ℝ) • scalarConvolution K g ξ) := by
    filter_upwards [angularDatum_ae s (SchwartzMap.smulLeftCLM ℂ (fun x => (χ x : ℂ)) φ)]
      with ξ hξ
    rw [hξ, hprod, angularFourier_mul X φ ξ, smul_comm]
    rfl
  -- assemble the `ℝ≥0∞` bound
  have hengine := eLpNorm_cutoff_multiplier_le hχ hc s g hmem
  have hstep :
      eLpNorm (angularDatum s (SchwartzMap.smulLeftCLM ℂ (fun x => (χ x : ℂ)) φ) : Space → ℂ)
          2 volume
        ≤ ENNReal.ofReal (d * cutoffMultiplierConst s χ) *
            eLpNorm (angularDatum s φ : Space → ℂ) 2 volume := by
    rw [eLpNorm_congr_ae hout]
    rw [show (fun ξ : Space => d • ((besselW s ξ : ℝ) • scalarConvolution K g ξ))
        = d • (fun ξ : Space => (besselW s ξ : ℝ) • scalarConvolution K g ξ) from rfl,
      eLpNorm_const_smul, Real.enorm_eq_ofReal hd0]
    calc ENNReal.ofReal d *
          eLpNorm (fun ξ : Space => (besselW s ξ : ℝ) • scalarConvolution K g ξ) 2 volume
        ≤ ENNReal.ofReal d * (ENNReal.ofReal (cutoffMultiplierConst s χ) *
            eLpNorm (fun η : Space => (besselW s η : ℝ) • g η) 2 volume) :=
          mul_le_mul' le_rfl hengine
      _ = ENNReal.ofReal (d * cutoffMultiplierConst s χ) *
            eLpNorm (angularDatum s φ : Space → ℂ) 2 volume := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hd0, hinput]
  -- convert to the real norms
  have hfin : ENNReal.ofReal (d * cutoffMultiplierConst s χ) *
      eLpNorm (angularDatum s φ : Space → ℂ) 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.memLp (angularDatum s φ)).2.ne
  have hreal :
      ‖angularDatum s (SchwartzMap.smulLeftCLM ℂ (fun x => (χ x : ℂ)) φ)‖
        ≤ (d * cutoffMultiplierConst s χ) * ‖angularDatum s φ‖ := by
    rw [Lp.norm_def, Lp.norm_def]
    have := ENNReal.toReal_mono hfin hstep
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (mul_nonneg hd0 (cutoffMultiplierConst_nonneg s χ))] at this
  refine hreal.trans ?_
  have hnn : (0:ℝ) ≤ ‖angularDatum s φ‖ := norm_nonneg _
  have hexp : cutoffFieldConst s χ * ‖angularDatum s φ‖
      = d * cutoffMultiplierConst s χ * ‖angularDatum s φ‖ + ‖angularDatum s φ‖ := by
    rw [cutoffFieldConst, ← hdd]; ring
  rw [hexp]; linarith

/-! ## 4. The cutoff multiplier on all angular `L²` data -/

/-- **Multiplication by the cutoff `χ` on the whole angular datum space.**  It is
the continuous `ℝ`-linear extension of `φ ↦ angularDatum s (χ·φ)` along the dense
range of `angularDatumL s` (`LinearMap.extendOfNorm`, the pattern of
`Paper3/CompleteTameProduct.lean`). -/
def cutoffOperator (χ : Space → ℝ) (s : ℝ) :
    Lp ℂ 2 (volume : Measure Space) →L[ℝ] Lp ℂ 2 (volume : Measure Space) :=
  LinearMap.extendOfNorm
    (((angularDatumL s).toLinearMap).comp
      (((SchwartzMap.smulLeftCLM ℂ (fun x => (χ x : ℂ))).toLinearMap).restrictScalars ℝ))
    ((angularDatumL s).toLinearMap)

theorem cutoffOperator_datum {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (s : ℝ) (φ : SchwartzMap Space ℂ) :
    cutoffOperator χ s (angularDatum s φ)
      = angularDatum s (SchwartzMap.smulLeftCLM ℂ (fun x => (χ x : ℂ)) φ) :=
  LinearMap.extendOfNorm_eq (denseRange_angularDatumL s)
    ⟨cutoffFieldConst s χ, norm_angularDatum_smulLeft_le hχ hc s⟩ φ

theorem norm_cutoffOperator_le {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (s : ℝ) (l : Lp ℂ 2 (volume : Measure Space)) :
    ‖cutoffOperator χ s l‖ ≤ cutoffFieldConst s χ * ‖l‖ :=
  LinearMap.norm_extendOfNorm_apply_le (denseRange_angularDatumL s) (cutoffFieldConst s χ)
    (norm_angularDatum_smulLeft_le hχ hc s) l

/-! ## 5. The graph and the reality of the cutoff operator -/

/-- Distributional multiplication by a temperate-growth symbol agrees with the
Schwartz product on Schwartz distributions. -/
theorem smulLeftCLM_schwartz {g : Space → ℂ} (hg : g.HasTemperateGrowth)
    (φ : SchwartzMap Space ℂ) :
    TemperedDistribution.smulLeftCLM ℂ g (φ : 𝓢'(Space, ℂ))
      = ((SchwartzMap.smulLeftCLM ℂ g φ : SchwartzMap Space ℂ) : 𝓢'(Space, ℂ)) := by
  ext ψ
  change (∫ x : Space, (SchwartzMap.smulLeftCLM ℂ g ψ) x • (φ : Space → ℂ) x)
      = ∫ x : Space, (ψ : Space → ℂ) x • (SchwartzMap.smulLeftCLM ℂ g φ) x
  simp only [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))

/-- **The graph of the cutoff operator.**  Its realization is exactly the
distributional product with `χ`. -/
theorem angularRealization_cutoffOperator {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (s : ℝ) (l : Lp ℂ 2 (volume : Measure Space)) :
    angularRealization s (cutoffOperator χ s l)
      = TemperedDistribution.smulLeftCLM ℂ (fun x => (χ x : ℂ)) (angularRealization s l) := by
  refine (denseRange_angularDatumL s).induction_on l
    (isClosed_eq ((angularRealization s).continuous.comp (cutoffOperator χ s).continuous)
      ((TemperedDistribution.smulLeftCLM ℂ (fun x => (χ x : ℂ))).continuous.comp
        (angularRealization s).continuous)) ?_
  intro φ
  simp only [angularDatumL_apply]
  rw [cutoffOperator_datum hχ hc, angularRealization_datum, angularRealization_datum,
    smulLeftCLM_schwartz (cutoff_hasTemperateGrowth hχ hc)]

/-- Conjugate reflection of an angular datum is the angular datum of the
conjugate Schwartz function. -/
theorem realSymmetry_angularDatum (s : ℝ) (φ : SchwartzMap Space ℂ) :
    realSymmetry (angularDatum s φ) = angularDatum s (conjugateSchwartz φ) := by
  change realSymmetry (angularFrequencyDilation (angularWeightEquiv s (weightedFourierLp s φ)))
    = angularFrequencyDilation (angularWeightEquiv s (weightedFourierLp s (conjugateSchwartz φ)))
  rw [weightedFourierLp_conjugate, ← angularWeightEquiv_realSymmetry,
    angularFrequencyDilation_realSymmetry]

/-- The cutoff operator commutes with conjugate reflection, because `χ` is
real-valued. -/
theorem realSymmetry_cutoffOperator {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (s : ℝ) (l : Lp ℂ 2 (volume : Measure Space)) :
    realSymmetry (cutoffOperator χ s l) = cutoffOperator χ s (realSymmetry l) := by
  refine (denseRange_angularDatumL s).induction_on l
    (isClosed_eq (realSymmetry.continuous.comp (cutoffOperator χ s).continuous)
      ((cutoffOperator χ s).continuous.comp realSymmetry.continuous)) ?_
  intro φ
  have hconj : conjugateSchwartz (SchwartzMap.smulLeftCLM ℂ (fun x => (χ x : ℂ)) φ)
      = SchwartzMap.smulLeftCLM ℂ (fun x => (χ x : ℂ)) (conjugateSchwartz φ) := by
    ext x
    rw [conjugateSchwartz_apply,
      SchwartzMap.smulLeftCLM_apply_apply (cutoff_hasTemperateGrowth hχ hc),
      SchwartzMap.smulLeftCLM_apply_apply (cutoff_hasTemperateGrowth hχ hc),
      conjugateSchwartz_apply, smul_eq_mul, smul_eq_mul, map_mul, Complex.conj_ofReal]
  simp only [angularDatumL_apply]
  rw [cutoffOperator_datum hχ hc, realSymmetry_angularDatum, realSymmetry_angularDatum,
    cutoffOperator_datum hχ hc, hconj]

/-- The cutoff operator preserves the real subspace. -/
theorem cutoffOperator_mem_realSubspace {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (s : ℝ) {l : FourierData} (hl : l ∈ realSubspace s) :
    cutoffOperator χ s l ∈ realSubspace s := by
  rw [mem_realSubspace_iff, realSymmetry_cutoffOperator hχ hc, (mem_realSubspace_iff s l).mp hl]

/-! ## 6. The verbatim `cutoffMultiplier` field -/

/-- **`BoundedDomainNormAPI.cutoffMultiplier` (`Section3/T22/Domain.lean`).**  For
every real order `s` and every smooth compactly supported cutoff `χ` there is a
positive constant `C` such that every Sobolev datum `A` has a cutoff datum `B`
(the transposed `smulLeftCLM` graph `IsCutoffDatum`) with `‖B‖ₑ ≤ C · ‖A‖ₑ`.

Route: `cutoffOperator χ s` is the continuous `ℝ`-linear extension of the
Schwartz-core cutoff product, bounded by `cutoffFieldConst s χ`
(`norm_cutoffOperator_le`, resting on the lane-397 engine), its realization is
the distributional product with `χ` (`angularRealization_cutoffOperator`), and it
preserves conjugate-reflection reality (`cutoffOperator_mem_realSubspace`); the
vector assembly is the `PiLp 2` Pythagoras `PiLp.norm_eq_of_L2`. -/
theorem cutoffMultiplier : ∀ (s : ℝ) (χ : Space → ℝ),
    ContDiff ℝ ∞ χ → HasCompactSupport χ →
    ∃ C : ℝ, 0 < C ∧ ∀ A : RealVectorSobolev s,
      ∃ B : RealVectorSobolev s,
        IsCutoffDatum s χ A B ∧ ‖B‖ₑ ≤ ENNReal.ofReal C * ‖A‖ₑ := by
  intro s χ hχ hc
  refine ⟨cutoffFieldConst s χ, cutoffFieldConst_pos s χ, fun A => ?_⟩
  refine ⟨WithLp.toLp 2 (fun i : Fin 3 =>
      (⟨cutoffOperator χ s ((A i : FourierData)),
        cutoffOperator_mem_realSubspace hχ hc s (A i).2⟩ : RealSobolevHilbert s)), ?_, ?_⟩
  · intro i ψ
    show angularRealization s (cutoffOperator χ s ((A i : FourierData))) ψ = _
    rw [angularRealization_cutoffOperator hχ hc,
      TemperedDistribution.smulLeftCLM_apply_apply]
  · set B : RealVectorSobolev s := WithLp.toLp 2 (fun i : Fin 3 =>
      (⟨cutoffOperator χ s ((A i : FourierData)),
        cutoffOperator_mem_realSubspace hχ hc s (A i).2⟩ : RealSobolevHilbert s)) with hB
    have hcomp : ∀ i : Fin 3, ‖B i‖ ≤ cutoffFieldConst s χ * ‖A i‖ := fun i =>
      norm_cutoffOperator_le hχ hc s ((A i : FourierData))
    have hsum : ∑ i : Fin 3, ‖B i‖ ^ 2
        ≤ (cutoffFieldConst s χ) ^ 2 * ∑ i : Fin 3, ‖A i‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have h1 := hcomp i
      have h2 : (0:ℝ) ≤ ‖A i‖ := norm_nonneg _
      have h3 : (0:ℝ) ≤ ‖B i‖ := norm_nonneg _
      nlinarith [h1, h2, h3]
    have hnormB : ‖B‖ ≤ cutoffFieldConst s χ * ‖A‖ := by
      rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2,
        show cutoffFieldConst s χ * Real.sqrt (∑ i : Fin 3, ‖A i‖ ^ 2)
          = Real.sqrt ((cutoffFieldConst s χ) ^ 2 * ∑ i : Fin 3, ‖A i‖ ^ 2) by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (cutoffFieldConst_pos s χ).le]]
      exact Real.sqrt_le_sqrt hsum
    calc ‖B‖ₑ = ENNReal.ofReal ‖B‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (cutoffFieldConst s χ * ‖A‖) := ENNReal.ofReal_le_ofReal hnormB
      _ = ENNReal.ofReal (cutoffFieldConst s χ) * ENNReal.ofReal ‖A‖ :=
          ENNReal.ofReal_mul (cutoffFieldConst_pos s χ).le
      _ = ENNReal.ofReal (cutoffFieldConst s χ) * ‖A‖ₑ := by rw [ofReal_norm]

end NSFormalization.Section3.T22
