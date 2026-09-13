import NavierStokes.NativeDyadicRegularity
import NavierStokes.HarmonicSourceSupport

/-!
# Flatness of the actual corrected initial coefficients at dyadic faces

The faces refer to the original label's native scale. The actual curl
correction is differentiated on the positive radial chart and is handled by
its zero germ at nonpositive radius. The source conclusions below concern
the literal harmonic differential residual.
-/

noncomputable section

namespace NavierStokes.InitialDyadicSource

open Set Filter Function CorrectionInitialization NativeDyadicRegularity
open HarmonicCalculus
open CurlClassBounds hiding ComplexVector
open scoped Topology ContDiff BigOperators ComplexConjugate

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl n

section FlatCalculus

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem flat_zero (x : D) : FlatAt (fun _ : D => (0 : E)) x :=
  FlatAt.of_germ Filter.EventuallyEq.rfl

theorem flat_add {f g : D → E} {x : D} (hf : FlatAt f x) (hg : FlatAt g x) :
    FlatAt (fun y => f y + g y) x := by
  refine ⟨hf.smooth.add hg.smooth, fun n => ?_⟩
  rw [fun_iteratedFDeriv_add_apply (hf.smooth.of_le (nat_le_infty n))
    (hg.smooth.of_le (nat_le_infty n)), hf.jets n, hg.jets n, add_zero]

theorem flat_neg {f : D → E} {x : D} (hf : FlatAt f x) : FlatAt (fun y => -f y) x := by
  simpa only [Function.comp_def, _root_.neg_apply, ContinuousLinearMap.id_apply] using
    hf.map (-ContinuousLinearMap.id ℝ E)

theorem flat_sub {f g : D → E} {x : D} (hf : FlatAt f x) (hg : FlatAt g x) :
    FlatAt (fun y => f y - g y) x := by
  simpa only [sub_eq_add_neg] using flat_add hf (flat_neg hg)

theorem flat_sum {ι : Type*} (s : Finset ι) {f : ι → D → E} {x : D}
    (hf : ∀ i ∈ s, FlatAt (f i) x) : FlatAt (fun y => ∑ i ∈ s, f i y) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using flat_zero (E := E) x
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      flat_add (hf i (Finset.mem_insert_self i s))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem flat_along {f : D → E} {V : D → D} {x : D}
    (hf : FlatAt f x) (hV : ContDiffAt ℝ ∞ V x) : FlatAt (along V f) x := by
  exact FlatAt.bilinear_left (ContinuousLinearMap.apply ℝ E).flip hf.fderiv hV

theorem flat_mul_left {f g : D → ℂ} {x : D}
    (hf : FlatAt f x) (hg : ContDiffAt ℝ ∞ g x) : FlatAt (fun y => f y * g y) x :=
  FlatAt.bilinear_left (ContinuousLinearMap.mul ℝ ℂ) hf hg

theorem flat_mul_right {f g : D → ℂ} {x : D}
    (hf : ContDiffAt ℝ ∞ f x) (hg : FlatAt g x) : FlatAt (fun y => f y * g y) x :=
  FlatAt.bilinear_right (ContinuousLinearMap.mul ℝ ℂ) hf hg

theorem flat_conj {f : D → ℂ} {x : D} (hf : FlatAt f x) :
    FlatAt (fun y => conj (f y)) x :=
  hf.map (Complex.conjCLE : ℂ →L[ℝ] ℂ)

theorem flat_component {f : D → ComplexVector} {x : D} (hf : FlatAt f x) (i : Fin 3) :
    FlatAt (fun y => f y i) x := hf.map (ContinuousLinearMap.proj i)

theorem flat_vector {f : D → ComplexVector} {x : D}
    (hf : ∀ i : Fin 3, FlatAt (fun y => f y i) x) : FlatAt f x := by
  have hs := flat_sum Finset.univ (fun i _ =>
    (hf i).map (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i))
  have he : (fun y => ∑ i : Fin 3,
      (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i) (f y i)) = f := by
    funext y
    ext i
    simp
  exact he ▸ hs

theorem flat_normalCoefficient {N : D → RealVector} {a : D → ComplexVector} {x : D}
    (hN : ContDiffAt ℝ ∞ N x) (ha : FlatAt a x) (hne : N x ≠ 0) :
    FlatAt (fun y => normalCoefficient (N y) (a y)) x := by
  have hn : ContDiffAt ℝ ∞ (fun y => (‖N y‖ ^ 2)⁻¹) x :=
    ((contDiff_norm_sq ℝ).contDiffAt.comp x hN).inv
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))
  exact FlatAt.smul hn (FlatAt.bilinear_right complexCrossLinear
    (complexify.contDiff.contDiffAt.comp x hN) ha)

theorem flat_cylindricalCurl {U : Set D} {R : D → ℝ} {Vr Vθ Vz : D → D}
    (G : CylindricalGeometry U R Vr Vθ Vz) {a : D → ComplexVector} {x : D}
    (ha : FlatAt a x) (hx : x ∈ U) : FlatAt (cylindricalCurl R Vr Vθ Vz a) x := by
  have hr := (G.radius_smooth.contDiffAt (G.isOpen.mem_nhds hx)).inv (G.radius_ne x hx)
  have hVr := G.radial_smooth.contDiffAt (G.isOpen.mem_nhds hx)
  have hVθ := G.angular_smooth.contDiffAt (G.isOpen.mem_nhds hx)
  have hVz := G.axial_smooth.contDiffAt (G.isOpen.mem_nhds hx)
  apply flat_vector
  intro i
  fin_cases i
  · exact flat_sub (FlatAt.smul hr (flat_along (flat_component ha 2) hVθ))
      (flat_along (flat_component ha 1) hVz)
  · exact flat_sub (flat_along (flat_component ha 0) hVz)
      (flat_along (flat_component ha 2) hVr)
  · exact flat_sub (flat_add (flat_along (flat_component ha 1) hVr)
      (FlatAt.smul hr (flat_component ha 1)))
      (FlatAt.smul hr (flat_along (flat_component ha 0) hVθ))

theorem flat_curlRemainder {U : Set D} {R : D → ℝ} {Vr Vθ Vz : D → D}
    (G : CylindricalGeometry U R Vr Vθ Vz) {a : D → ComplexVector} {x : D}
    (ha : FlatAt a x) (hx : x ∈ U) (K : ℝ) : FlatAt (curlRemainder K R Vr Vθ Vz a) x := by
  exact ((flat_cylindricalCurl G ha hx).map
    (Complex.I • ContinuousLinearMap.id ℝ ComplexVector)).const_smul (1 / K)

end FlatCalculus

abbrev Point := LocalSignedRequest.Point
abbrev FullPoint := ActualPrimary.FullPoint
abbrev Index (B N0 : ℕ) := ActualInitialization.Index B N0

section InitialCoefficients

variable {B N0 : ℕ}

theorem initial_corrected_flat_positive (l : Index B N0) (n : ℕ) {x : FullPoint}
    (hT : 0 < x.1.2.1.1) (hR : 0 < x.1.1)
    (he : ActualCoreSupport.nativeQ l n x.1 = 1 / 2 ∨ ActualCoreSupport.nativeQ l n x.1 = 2) :
    FlatAt ((ActualInitialization.primaryPiece l).exactCoefficients.amplitude n) x := by
  let p := ActualInitialization.primaryPiece l
  have hx : x ∈ ActualPrimaryCoherence.positiveRadialChart := ⟨hR, hT⟩
  have G := ActualPrimaryCoherence.piece_geometry ActualPrimary.standardRegion B n
  have hΦ := ActualPrimaryCoherence.chart_phase_smooth l.2 l.1 n
  have hN := (phaseNormal_contDiffOn G hΦ).contDiffAt (G.isOpen.mem_nhds hx)
  have hne := ActualPrimaryCoherence.piece_normal_ne ActualPrimary.standardRegion l.2 l.1 n hx
  have ha := (initial_cut_flat l n hT he).1
  have hc := flat_normalCoefficient hN ha hne
  have hr := flat_curlRemainder G hc hx (p.coefficients.frequency n)
  exact flat_add ha hr

/-- At nonpositive radius the actual cut coefficient is zero on a full
neighborhood, so the same is true of the actual curl-corrected amplitude. -/
theorem initial_corrected_zero_germ_nonpositive (l : Index B N0) (n : ℕ) {x : FullPoint}
    (hT : 0 < x.1.2.1.1) (hR : x.1.1 ≤ 0) :
    (ActualInitialization.primaryPiece l).exactCoefficients.amplitude n =ᶠ[𝓝 x] fun _ => 0 := by
  have hout : x.1 ∉ ActualCoreSupport.refinedCarrier l n := by
    intro hx
    have hl := ((ActualCoreSupport.mem_refinedCarrier_iff l n hT).mp hx).2.1.1
    have hn : ActualCoreSupport.radialRatio x.1 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hR (Real.sqrt_nonneg _)
    exact (not_lt_of_ge hn) ((PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal).trans_le hl)
  have ha := ActualCoreSupport.cut_amplitude_zero_germ l n hT hout
  exact notMem_tsupport_iff_eventuallyEq.mp
    (fun hs => (notMem_tsupport_iff_eventuallyEq.mpr ha)
      ((ActualInitialization.primaryPiece l).exactAmplitude_tsupport_subset_tangent n hs))

/-- All full tensors of both literal corrected coefficients vanish at either
label-reference dyadic face. The radial coordinate may be nonpositive. -/
theorem initial_corrected_flat (l : Index B N0) (n : ℕ) {x : FullPoint}
    (hT : 0 < x.1.2.1.1)
    (he : ActualCoreSupport.nativeQ l n x.1 = 1 / 2 ∨ ActualCoreSupport.nativeQ l n x.1 = 2) :
    FlatAt ((ActualInitialization.primaryPiece l).exactCoefficients.amplitude n) x ∧
      FlatAt ((ActualInitialization.primaryPiece l).exactCoefficients.pressure n) x := by
  refine ⟨?_, (initial_cut_flat l n hT he).2⟩
  by_cases hR : 0 < x.1.1
  · exact initial_corrected_flat_positive l n hT hR he
  · exact FlatAt.of_germ (initial_corrected_zero_germ_nonpositive l n hT (le_of_not_gt hR))

end InitialCoefficients

section HarmonicFlatness

open HarmonicFields

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- All actual coefficient tensors vanish at the point. -/
def FlatCoefficients (c : Coefficients D) (x : D) : Prop := ∀ j : ℤ, FlatAt (c j) x

/-- Pointwise primitive coefficient regularity, without an output equation. -/
def SmoothCoefficientsAt (c : Coefficients D) (x : D) : Prop :=
  ∀ j : ℤ, ContDiffAt ℝ ∞ (c j) x

theorem smooth_along {f : D → ℂ} {V : D → D} {x : D}
    (hf : ContDiffAt ℝ ∞ f x) (hV : ContDiffAt ℝ ∞ V x) :
    ContDiffAt ℝ ∞ (along V f) x :=
  (hf.fderiv_right (by simp)).clm_apply hV

namespace SmoothCoefficientsAt

variable {x : D} {c d : Coefficients D}

theorem zero : SmoothCoefficientsAt (0 : Coefficients D) x := fun _ => contDiffAt_const

theorem add (hc : SmoothCoefficientsAt c x) (hd : SmoothCoefficientsAt d x) :
    SmoothCoefficientsAt (c + d) x := fun j => (hc j).add (hd j)

theorem neg (hc : SmoothCoefficientsAt c x) : SmoothCoefficientsAt (-c) x :=
  fun j => (hc j).neg

theorem mul (hc : SmoothCoefficientsAt c x) (hd : SmoothCoefficientsAt d x) :
    SmoothCoefficientsAt (c * d) x := by
  intro j
  have he : (c * d) j = fun y => ∑ k ∈ c.support, c k y * d (j - k) y := by
    funext y
    exact convolution_apply c d j y
  rw [he]
  exact ContDiffAt.sum (fun k _ => (hc k).mul (hd (j - k)))

theorem constant {f : D → ℂ} (hf : ContDiffAt ℝ ∞ f x) :
    SmoothCoefficientsAt (constantCoefficient f) x := by
  intro j
  by_cases hj : j = 0
  · subst j
    simpa only [constantCoefficient, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] using hf
  · simp only [constantCoefficient, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne hj]
    exact contDiffAt_const

theorem differentiate (hc : SmoothCoefficientsAt c x) {V : D → D} {Φ : D → ℝ}
    (hV : ContDiffAt ℝ ∞ V x) (hΦ : ContDiffAt ℝ ∞ Φ x) (k : ℝ) :
    SmoothCoefficientsAt (differentiate V k Φ c) x := by
  intro j
  have hs : ContDiffAt ℝ ∞ (fun y => ((HarmonicCalculus.along V Φ y : ℝ) : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x ((hΦ.fderiv_right (by simp)).clm_apply hV)
  exact (smooth_along (hc j) hV).add ((contDiffAt_const.mul hs).mul (hc j))

theorem angular (hc : SmoothCoefficientsAt c x) (kp : ℤ) :
    SmoothCoefficientsAt (angularDifferentiate kp c) x :=
  fun j => contDiffAt_const.mul (hc j)

end SmoothCoefficientsAt

namespace FlatCoefficients

variable {x : D} {c d : Coefficients D}

theorem smooth (hc : FlatCoefficients c x) : SmoothCoefficientsAt c x :=
  fun j => (hc j).smooth

theorem zero : FlatCoefficients (0 : Coefficients D) x := fun _ => flat_zero x

theorem add (hc : FlatCoefficients c x) (hd : FlatCoefficients d x) :
    FlatCoefficients (c + d) x := fun j => flat_add (hc j) (hd j)

theorem neg (hc : FlatCoefficients c x) : FlatCoefficients (-c) x :=
  fun j => flat_neg (hc j)

theorem sub (hc : FlatCoefficients c x) (hd : FlatCoefficients d x) :
    FlatCoefficients (c - d) x := fun j => flat_sub (hc j) (hd j)

theorem mul_right (hc : FlatCoefficients c x) (hd : SmoothCoefficientsAt d x) :
    FlatCoefficients (c * d) x := by
  intro j
  have he : (c * d) j = fun y => ∑ k ∈ c.support, c k y * d (j - k) y := by
    funext y
    exact convolution_apply c d j y
  rw [he]
  exact flat_sum c.support (fun k _ => flat_mul_left (hc k) (hd (j - k)))

theorem mul_left (hc : SmoothCoefficientsAt c x) (hd : FlatCoefficients d x) :
    FlatCoefficients (c * d) x := by
  intro j
  have he : (c * d) j = fun y => ∑ k ∈ c.support, c k y * d (j - k) y := by
    funext y
    exact convolution_apply c d j y
  rw [he]
  exact flat_sum c.support (fun k _ => flat_mul_right (hc k) (hd (j - k)))

theorem single {f : D → ℂ} (hf : FlatAt f x) (k : ℤ) :
    FlatCoefficients (AddMonoidAlgebra.single k f) x := by
  intro j
  by_cases hj : j = k
  · subst j
    simpa only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] using hf
  · simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne hj]
    exact flat_zero (E := ℂ) x

theorem conjugateReverse (hc : FlatCoefficients c x) : FlatCoefficients (conjugateReverse c) x := by
  intro j
  have he : HarmonicFields.conjugateReverse c j = fun y => conj (c (-j) y) := by
    funext y
    exact conjugateReverse_apply c j y
  rw [he]
  exact flat_conj (hc (-j))

theorem realProjection (hc : FlatCoefficients c x) :
    FlatCoefficients (HarmonicResidual.realCoefficients c) x := by
  intro j
  have he : HarmonicResidual.realCoefficients c j =
      fun y => (2 : ℂ)⁻¹ * (c j y + conj (c (-j) y)) := by
    funext y
    exact HarmonicResidual.realCoefficients_apply c j y
  rw [he]
  exact flat_mul_right contDiffAt_const (flat_add (hc j) (flat_conj (hc (-j))))

theorem nonconstant (hc : FlatCoefficients c x) :
    FlatCoefficients (HarmonicResidual.nonconstant c) x := by
  intro j
  by_cases hj : j = 0
  · subst j
    simp only [HarmonicResidual.nonconstant, AddMonoidAlgebra.coeff_erase, Finsupp.erase_same]
    exact flat_zero (E := ℂ) x
  · simpa only [HarmonicResidual.nonconstant, AddMonoidAlgebra.coeff_erase, Finsupp.erase_ne hj] using hc j

theorem differentiate (hc : FlatCoefficients c x) {V : D → D} {Φ : D → ℝ}
    (hV : ContDiffAt ℝ ∞ V x) (hΦ : ContDiffAt ℝ ∞ Φ x) (k : ℝ) :
    FlatCoefficients (differentiate V k Φ c) x := by
  intro j
  have hs : ContDiffAt ℝ ∞ (fun y => phaseFactor (k * (j : ℝ)) * ((HarmonicCalculus.along V Φ y : ℝ) : ℂ)) x :=
    contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp x
      ((hΦ.fderiv_right (by simp)).clm_apply hV))
  exact flat_add (flat_along (hc j) hV) (flat_mul_right hs (hc j))

theorem angular (hc : FlatCoefficients c x) (kp : ℤ) :
    FlatCoefficients (angularDifferentiate kp c) x :=
  fun j => flat_mul_right contDiffAt_const (hc j)

end FlatCoefficients

theorem flat_conjugatePair {f : D → ℂ} {x : D} (hf : FlatAt f x) (k : ℤ) :
    FlatCoefficients (ErrorHarmonics.conjugatePair k f) x := by
  have hs := FlatCoefficients.single
    (show FlatAt (fun y => f y / 2) x from by
      simpa only [div_eq_mul_inv] using flat_mul_left hf contDiffAt_const) k
  exact hs.add hs.conjugateReverse

end HarmonicFlatness

section InitialHarmonics

variable {B N0 : ℕ}

/-- Exact conjugate-pair extraction preserves the corrected full-coefficient
flatness, including the negative and zero harmonic cases. -/
theorem initial_harmonic_flat (l : Index B N0) (n : ℕ) {x : Point}
    (hT : 0 < x.2.1.1)
    (he : ActualCoreSupport.nativeQ l n x = 1 / 2 ∨ ActualCoreSupport.nativeQ l n x = 2) :
    (∀ i, FlatCoefficients ((ActualInitialization.primaryBlock l).velocity n i) x) ∧
      FlatCoefficients ((ActualInitialization.primaryBlock l).pressure n) x := by
  obtain ⟨ha, hp⟩ := initial_corrected_flat l n (x := (x, 0)) hT he
  refine ⟨fun i => ?_, ?_⟩
  · exact flat_conjugatePair ((flat_component ha i).comp (g := fun y : Point => (y, (0 : ℝ)))
      (HarmonicWaveInteraction.inclusion (D := Point)).contDiff) 1
  · exact flat_conjugatePair (hp.comp (g := fun y : Point => (y, (0 : ℝ)))
      (HarmonicWaveInteraction.inclusion (D := Point)).contDiff) 1

theorem initial_gaussian_harmonic_flat (l : Index B N0) (n : ℕ) {x : Point}
    (hT : 0 < x.2.1.1)
    (he : ActualCoreSupport.nativeQ l n x = 1 / 2 ∨ ActualCoreSupport.nativeQ l n x = 2) :
    ∀ i, FlatCoefficients ((ActualInitialization.gaussianBlock l).velocity n i) x := by
  intro i
  have hg := initial_chart_gaussian_flat l n (x := (x, 0)) hT he
  exact flat_conjugatePair ((flat_component hg i).comp (g := fun y : Point => (y, (0 : ℝ)))
    (HarmonicWaveInteraction.inclusion (D := Point)).contDiff) 1

end InitialHarmonics

section ResidualFlatness

open HarmonicFields

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem rotate_flat {a : HarmonicResidual.VectorCoefficients D} {x : D}
    (ha : ∀ i, FlatCoefficients (a i) x) :
    ∀ i, FlatCoefficients (HarmonicResidual.rotate a i) x := by
  intro i
  fin_cases i
  · exact (ha 1).neg
  · exact ha 0
  · exact FlatCoefficients.zero

theorem rotate_smooth {a : HarmonicResidual.VectorCoefficients D} {x : D}
    (ha : ∀ i, SmoothCoefficientsAt (a i) x) :
    ∀ i, SmoothCoefficientsAt (HarmonicResidual.rotate a i) x := by
  intro i
  fin_cases i
  · exact (ha 1).neg
  · exact ha 0
  · exact SmoothCoefficientsAt.zero

variable {U : Set D} {g : HarmonicResidual.Frame D} {x : D}
    (hU : IsOpen U) (hg : g.Regular U) (hx : x ∈ U)

include hU hg hx

theorem inverse_radius_smooth :
    SmoothCoefficientsAt (constantCoefficient (fun y => ((g.radius y)⁻¹ : ℝ) : D → ℂ)) x :=
  SmoothCoefficientsAt.constant (Complex.ofRealCLM.contDiff.contDiffAt.comp x
    ((hg.radius.contDiffAt (hU.mem_nhds hx)).inv (hg.radius_ne x hx)))

theorem inverse_radius_sq_smooth :
    SmoothCoefficientsAt (constantCoefficient (fun y => (((g.radius y) ^ 2)⁻¹ : ℝ) : D → ℂ)) x :=
  SmoothCoefficientsAt.constant (Complex.ofRealCLM.contDiff.contDiffAt.comp x
    (((hg.radius.contDiffAt (hU.mem_nhds hx)).pow 2).inv (pow_ne_zero 2 (hg.radius_ne x hx))))

theorem complex_inverse_radius_smooth :
    SmoothCoefficientsAt (constantCoefficient (fun y => (g.radius y : ℂ)⁻¹)) x := by
  simpa only [Complex.ofReal_inv] using inverse_radius_smooth hU hg hx

theorem scalarLaplacian_flat {Φ : D → ℝ} (hΦ : ContDiffAt ℝ ∞ Φ x) (k : ℝ) (kp : ℤ)
    {c : Coefficients D} (hc : FlatCoefficients c x) :
    FlatCoefficients (HarmonicResidual.scalarLaplacian g k Φ kp c) x := by
  have hr := hg.radial.contDiffAt (hU.mem_nhds hx)
  have hz := hg.axial.contDiffAt (hU.mem_nhds hx)
  exact ((((hc.differentiate hr hΦ k).differentiate hr hΦ k).add
    (FlatCoefficients.mul_left (inverse_radius_smooth hU hg hx) (hc.differentiate hr hΦ k))).add
      (FlatCoefficients.mul_left (inverse_radius_sq_smooth hU hg hx) ((hc.angular kp).angular kp))).add
        ((hc.differentiate hz hΦ k).differentiate hz hΦ k)

theorem vectorLaplacian_flat {Φ : D → ℝ} (hΦ : ContDiffAt ℝ ∞ Φ x) (k : ℝ) (kp : ℤ)
    {a : HarmonicResidual.VectorCoefficients D} (ha : ∀ i, FlatCoefficients (a i) x) :
    ∀ i, FlatCoefficients (HarmonicResidual.vectorLaplacian g k Φ kp a i) x := by
  intro i
  exact (scalarLaplacian_flat hU hg hx hΦ k kp (ha i)).add
    (FlatCoefficients.mul_left (inverse_radius_sq_smooth hU hg hx)
      ((FlatCoefficients.mul_left (SmoothCoefficientsAt.constant contDiffAt_const)
        (rotate_flat (fun j => (ha j).angular kp) i)).add (rotate_flat (rotate_flat ha) i)))

theorem transport_flat_right {Φ : D → ℝ} (hΦ : ContDiffAt ℝ ∞ Φ x) (k : ℝ) (kp : ℤ)
    {a b : HarmonicResidual.VectorCoefficients D}
    (ha : ∀ i, SmoothCoefficientsAt (a i) x) (hb : ∀ i, FlatCoefficients (b i) x) :
    ∀ i, FlatCoefficients (HarmonicResidual.transport g k Φ kp a b i) x := by
  intro i
  have hr := hg.radial.contDiffAt (hU.mem_nhds hx)
  have hz := hg.axial.contDiffAt (hU.mem_nhds hx)
  exact ((FlatCoefficients.mul_left (ha 0) ((hb i).differentiate hr hΦ k)).add
    (FlatCoefficients.mul_left ((ha 1).mul (complex_inverse_radius_smooth hU hg hx))
      (((hb i).angular kp).add (rotate_flat hb i)))).add
        (FlatCoefficients.mul_left (ha 2) ((hb i).differentiate hz hΦ k))

theorem transport_flat_left {Φ : D → ℝ} (hΦ : ContDiffAt ℝ ∞ Φ x) (k : ℝ) (kp : ℤ)
    {a b : HarmonicResidual.VectorCoefficients D}
    (ha : ∀ i, FlatCoefficients (a i) x) (hb : ∀ i, SmoothCoefficientsAt (b i) x) :
    ∀ i, FlatCoefficients (HarmonicResidual.transport g k Φ kp a b i) x := by
  intro i
  have hr := hg.radial.contDiffAt (hU.mem_nhds hx)
  have hz := hg.axial.contDiffAt (hU.mem_nhds hx)
  exact (((ha 0).mul_right ((hb i).differentiate hr hΦ k)).add
    (((ha 1).mul_right (complex_inverse_radius_smooth hU hg hx)).mul_right
      (((hb i).angular kp).add (rotate_smooth hb i)))).add
        ((ha 2).mul_right ((hb i).differentiate hz hΦ k))

theorem gradient_flat {Φ : D → ℝ} (hΦ : ContDiffAt ℝ ∞ Φ x) (k : ℝ) (kp : ℤ)
    {p : Coefficients D} (hp : FlatCoefficients p x) :
    ∀ i, FlatCoefficients (HarmonicResidual.gradient g k Φ kp p i) x := by
  intro i
  fin_cases i
  · exact hp.differentiate (hg.radial.contDiffAt (hU.mem_nhds hx)) hΦ k
  · exact FlatCoefficients.mul_left (inverse_radius_smooth hU hg hx) (hp.angular kp)
  · exact hp.differentiate (hg.axial.contDiffAt (hU.mem_nhds hx)) hΦ k

/-- The literal second-order nonlinear differential polynomial preserves
flatness of its perturbation inputs against a smooth primitive background. -/
theorem nonlinearResidual_flat {Φ : D → ℝ} (hΦ : ContDiffAt ℝ ∞ Φ x) (k : ℝ) (kp : ℤ)
    {B a : HarmonicResidual.VectorCoefficients D} {p : Coefficients D}
    (hB : ∀ i, SmoothCoefficientsAt (B i) x)
    (ha : ∀ i, FlatCoefficients (a i) x) (hp : FlatCoefficients p x) :
    ∀ i, FlatCoefficients (HarmonicResidual.nonlinearResidual g k Φ kp B a p i) x := by
  intro i
  exact (((((ha i).differentiate (hg.time.contDiffAt (hU.mem_nhds hx)) hΦ k).add
    (transport_flat_right hU hg hx hΦ k kp hB ha i)).add
      (transport_flat_left hU hg hx hΦ k kp ha hB i)).add
        (gradient_flat hU hg hx hΦ k kp hp i) |>.sub
          (FlatCoefficients.mul_left (SmoothCoefficientsAt.constant contDiffAt_const)
            (vectorLaplacian_flat hU hg hx hΦ k kp ha i))).add
              (transport_flat_right hU hg hx hΦ k kp (fun j => (ha j).smooth) ha i)

omit hg in
/-- Flatness of the actual grouped source follows from primitive frame,
background, coefficient, and excluded-error data. No residual regularity or
vanishing is assumed. -/
theorem residualBlock_flat (c : CorrectionState.Context D) (s : CorrectionState.State D)
    (b : CorrectionState.HarmonicBlock D) (G A : HarmonicResidual.BlockCoefficients D) (n : ℕ)
    (hframe : (HarmonicResidual.contextFrame c n).Regular U)
    (hΦ : ContDiffAt ℝ ∞ (b.phase n) x)
    (hbackground : ∀ i, ContDiffAt ℝ ∞
      (fun y => HarmonicResidual.contextBase c n y i + HarmonicResidual.stateMean s n y i) x)
    (hv : ∀ i, FlatCoefficients (b.velocity n i) x) (hp : FlatCoefficients (b.pressure n) x)
    (hG : ∀ i, FlatCoefficients (G n i) x) (hA : ∀ i, FlatCoefficients (A n i) x) :
    ∀ i, FlatCoefficients ((HarmonicResidual.residualBlock c s b G A).velocity n i) x := by
  have hN := nonlinearResidual_flat hU hframe hx hΦ (b.frequency n) (b.angularFrequency n)
    (fun i => SmoothCoefficientsAt.constant (hbackground i))
    (fun i => (hv i).realProjection) hp.realProjection
  intro i
  exact (((hN i).sub (hG i)).sub (hA i)).realProjection.nonconstant

end ResidualFlatness

section ActualSource

noncomputable def positiveTime : Set Point := {x | 0 < x.2.1.1}

noncomputable def positiveRadialTime : Set Point := {x | 0 < x.1 ∧ 0 < x.2.1.1}

theorem positiveTime_open : IsOpen positiveTime :=
  isOpen_lt continuous_const continuous_snd.fst.fst

theorem positiveRadialTime_open : IsOpen positiveRadialTime :=
  (isOpen_lt continuous_const continuous_fst).inter positiveTime_open

theorem actual_frame_regular (B n : ℕ) :
    (HarmonicResidual.contextFrame (ActualPrimary.commonContext B) n).Regular positiveRadialTime := by
  apply HarmonicResidual.contextFrame_regular
  · exact contDiffOn_fst
  · intro x hx
    exact hx.1.ne'
  · intro x hx
    change ContDiffWithinAt ℝ ∞ (fun y : Point =>
      ChartScales.radialExponent ActualPrimary.h * y.1 ^ (ChartScales.radialExponent ActualPrimary.h - 1))
      positiveRadialTime x
    exact (contDiffAt_const.mul (contDiffAt_fst.rpow_const_of_ne hx.1.ne')).contDiffWithinAt

theorem actual_base_smoothAt (B n : ℕ) {x : Point} (hT : 0 < x.2.1.1) (hR : 0 < x.1) :
    ∀ i, ContDiffAt ℝ ∞ (fun y => HarmonicResidual.contextBase (ActualPrimary.commonContext B) n y i) x := by
  let U : Set TorusInverse.Plane := {p | 0 < p.1}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_fst
  have hb := BaseContextAssembly.base_smooth ActualPrimary.certificate ActualPrimary.modulation
    ActualPrimary.upper B U (fun _ hp => hp)
  have hx : x ∈ LocalRankDefect.positiveDomain U := ⟨hR, hT⟩
  have hn := (LocalRankDefect.positiveDomain_open hU).mem_nhds hx
  intro i
  fin_cases i
  · exact Complex.ofRealCLM.contDiff.contDiffAt.comp x ((hb.radial n).contDiffAt hn)
  · exact Complex.ofRealCLM.contDiff.contDiffAt.comp x ((hb.angular n).contDiffAt hn)
  · exact Complex.ofRealCLM.contDiff.contDiffAt.comp x ((hb.axial n).contDiffAt hn)

variable {B N0 : ℕ}

/-- The actual refined support statement holds on the full positive-time
domain, including both label-reference dyadic faces. -/
theorem initial_inputSupport_positive (l : Index B N0) :
    HarmonicSourceSupport.InputSupportOn positiveTime (ActualCoreSupport.refinedCarrier l)
      (ActualInitialization.primaryBlock l) (ActualInitialization.gaussianBlock l).velocity 0 := by
  apply HarmonicSourceSupport.InputSupportOn.of_fields _ _ _
    (ActualInitialization.angularMode_ne_zero l)
  · intro n x hx hn θ i
    exact congrFun (ActualCoreSupport.primary_velocity_zero l n hx hn θ) i
  · intro n x hx hn θ
    exact ActualCoreSupport.primary_pressure_zero l n hx hn θ
  · intro n x hx hn θ i
    exact congrFun (ActualCoreSupport.gaussian_velocity_zero l n hx hn θ) i
  · intro n x hx hn θ i
    simp [HarmonicResidual.vectorField, HarmonicResidual.field_zero]

theorem nonpositive_not_refined (l : Index B N0) (n : ℕ) {x : Point}
    (hT : 0 < x.2.1.1) (hR : x.1 ≤ 0) : x ∉ ActualCoreSupport.refinedCarrier l n := by
  intro hx
  have hl := ((ActualCoreSupport.mem_refinedCarrier_iff l n hT).mp hx).2.1.1
  have hn : ActualCoreSupport.radialRatio x ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hR (Real.sqrt_nonneg _)
  exact (not_lt_of_ge hn) ((PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal).trans_le hl)

/-- Locality of the actual harmonic differential source handles nonpositive
radius. No inverse-radius smoothness or background regularity is assumed. -/
theorem initial_source_zero_germ_nonpositive (s : CorrectionState.State Point)
    (l : Index B N0) (n : ℕ) {x : Point} (hT : 0 < x.2.1.1) (hR : x.1 ≤ 0) (j : ℤ) :
    ParticularWaveAssembly.residualSource (ActualPrimary.commonContext B) s
      (ActualInitialization.primaryBlock l) (ActualInitialization.gaussianBlock l).velocity 0 j n
        =ᶠ[𝓝 x] fun _ => 0 :=
  HarmonicSourceSupport.residualSource_zero_germ_on _ _ _ _ _ positiveTime_open
    (ActualCoreSupport.refinedCarrier_closed l) (initial_inputSupport_positive l) j n hT
    (nonpositive_not_refined l n hT hR)

/-- At positive radius only the primitive mean background remains an input.
The graph directions, base, phase, corrected wave and Gaussian flatness are
all proved for the literal initial family. -/
theorem initial_residual_flat_positive (s : CorrectionState.State Point)
    (l : Index B N0) (n : ℕ) {x : Point} (hT : 0 < x.2.1.1) (hR : 0 < x.1)
    (he : ActualCoreSupport.nativeQ l n x = 1 / 2 ∨ ActualCoreSupport.nativeQ l n x = 2)
    (hmean : ∀ i, ContDiffAt ℝ ∞ (fun y => HarmonicResidual.stateMean s n y i) x) :
    ∀ i, FlatCoefficients ((HarmonicResidual.residualBlock (ActualPrimary.commonContext B) s
      (ActualInitialization.primaryBlock l) (ActualInitialization.gaussianBlock l).velocity 0).velocity n i) x := by
  obtain ⟨hv, hp⟩ := initial_harmonic_flat l n hT he
  have hfull := (ActualPrimaryCoherence.chart_phase_smooth l.2 l.1 n).contDiffAt
      (ActualPrimaryCoherence.positiveRadialChart_open.mem_nhds
        (show (x, (0 : ℝ)) ∈ ActualPrimaryCoherence.positiveRadialChart from ⟨hR, hT⟩))
  have hΦ : ContDiffAt ℝ ∞ ((ActualInitialization.primaryBlock l).phase n) x := by
    change ContDiffAt ℝ ∞ (fun y : Point => (ActualPrimary.chartCoefficients l.2 l.1).phase n (y, 0)) x
    exact hfull.comp x (show ContDiffAt ℝ ∞ (fun y : Point => (y, (0 : ℝ))) x from
      contDiffAt_id.prodMk contDiffAt_const)
  exact residualBlock_flat positiveRadialTime_open (show x ∈ positiveRadialTime from ⟨hR, hT⟩)
    (ActualPrimary.commonContext B) s (ActualInitialization.primaryBlock l)
    (ActualInitialization.gaussianBlock l).velocity 0 n (actual_frame_regular B n) hΦ
    (fun i => (actual_base_smoothAt B n hT hR i).add (hmean i)) hv hp
    (initial_gaussian_harmonic_flat l n hT he) (fun _ => FlatCoefficients.zero)

/-- All coefficients of the actual initial source are smooth and flat at
either dyadic face. At nonpositive radius this follows from a zero germ;
on the positive branch the only hypothesis concerns the primitive mean. -/
theorem initial_residual_flat (s : CorrectionState.State Point)
    (l : Index B N0) (n : ℕ) {x : Point} (hT : 0 < x.2.1.1)
    (he : ActualCoreSupport.nativeQ l n x = 1 / 2 ∨ ActualCoreSupport.nativeQ l n x = 2)
    (hmean : 0 < x.1 → ∀ i, ContDiffAt ℝ ∞ (fun y => HarmonicResidual.stateMean s n y i) x) :
    ∀ i, FlatCoefficients ((HarmonicResidual.residualBlock (ActualPrimary.commonContext B) s
      (ActualInitialization.primaryBlock l) (ActualInitialization.gaussianBlock l).velocity 0).velocity n i) x := by
  by_cases hr : 0 < x.1
  · exact initial_residual_flat_positive s l n hT hr he (hmean hr)
  · intro i j
    have hz := initial_source_zero_germ_nonpositive s l n hT (le_of_not_gt hr) j
    have hi : (HarmonicResidual.residualBlock (ActualPrimary.commonContext B) s
        (ActualInitialization.primaryBlock l) (ActualInitialization.gaussianBlock l).velocity 0).velocity n i j
        =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hz] with y hy
      exact congrFun hy i
    exact FlatAt.of_germ hi

theorem initial_source_flat (s : CorrectionState.State Point)
    (l : Index B N0) (n : ℕ) {x : Point} (hT : 0 < x.2.1.1)
    (he : ActualCoreSupport.nativeQ l n x = 1 / 2 ∨ ActualCoreSupport.nativeQ l n x = 2)
    (hmean : 0 < x.1 → ∀ i, ContDiffAt ℝ ∞ (fun y => HarmonicResidual.stateMean s n y i) x) (j : ℤ) :
    FlatAt (ParticularWaveAssembly.residualSource (ActualPrimary.commonContext B) s
      (ActualInitialization.primaryBlock l) (ActualInitialization.gaussianBlock l).velocity 0 j n) x :=
  flat_vector (fun i => initial_residual_flat s l n hT he hmean i j)

/-- The previously constructed mean supplies its primitive smoothness on
the actual open common slow domain. This does not extend that domain over
its own dyadic boundary. -/
theorem initialized_mean_smoothAt (B N0 n : ℕ) {x : Point}
    (hx : x.2.1 ∈ ActualPrimary.standardRegion.carrier) :
    ∀ i, ContDiffAt ℝ ∞
      (fun y => HarmonicResidual.stateMean (ActualInitialization.initialState B N0) n y i) x := by
  have hm : MeanIncrementBounds.SmoothTriple
      (PhysicalMeanDomain.slowDomain ActualPrimary.standardRegion.carrier)
      (ActualInitialization.initialState B N0).mean :=
    ActualInitialMean.initial_mean_smooth B N0
  have hn := (PhysicalMeanDomain.slowDomain_open ActualPrimary.standardRegion.isOpen).mem_nhds hx
  intro i
  fin_cases i
  · exact Complex.ofRealCLM.contDiff.contDiffAt.comp x ((hm.radial n).contDiffAt hn)
  · exact Complex.ofRealCLM.contDiff.contDiffAt.comp x ((hm.angular n).contDiffAt hn)
  · exact Complex.ofRealCLM.contDiff.contDiffAt.comp x ((hm.axial n).contDiffAt hn)

theorem initialResidualBlock_flat_on_common (l : Index B N0) (n : ℕ) {x : Point}
    (hx : x.2.1 ∈ ActualPrimary.standardRegion.carrier)
    (he : ActualCoreSupport.nativeQ l n x = 1 / 2 ∨ ActualCoreSupport.nativeQ l n x = 2) :
    ∀ i, FlatCoefficients ((ActualInitialization.initialResidualBlock l).velocity n i) x :=
  initial_residual_flat (ActualInitialization.initialState B N0) l n
    (ActualPrimary.standardRegion.time_pos _ hx) he
    (fun _ => initialized_mean_smoothAt B N0 n hx)

theorem initialized_source_flat_on_common (l : Index B N0) (n : ℕ) {x : Point}
    (hx : x.2.1 ∈ ActualPrimary.standardRegion.carrier)
    (he : ActualCoreSupport.nativeQ l n x = 1 / 2 ∨ ActualCoreSupport.nativeQ l n x = 2) (j : ℤ) :
    FlatAt (ParticularWaveAssembly.residualSource (ActualPrimary.commonContext B)
      (ActualInitialization.initialState B N0) (ActualInitialization.primaryBlock l)
      (ActualInitialization.gaussianBlock l).velocity 0 j n) x :=
  initial_source_flat (ActualInitialization.initialState B N0) l n
    (ActualPrimary.standardRegion.time_pos _ hx) he
    (fun _ => initialized_mean_smoothAt B N0 n hx) j

end ActualSource

end NavierStokes.InitialDyadicSource
