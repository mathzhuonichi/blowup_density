import NSFormalization.Section4.R43.Trilinear
import NSFormalization.Section4.D01.FiniteOrderConstructor
import NSFormalization.Section4.D01.LerayLowering
import Euler.MeanOrbitSmoothL2Field
import Formal.R3FourierConjugationBridge
import Formal.R3H2CoordinateFourierBounds

/-!
# Physical and datum-level order shifts at the critical exponent

This module supplies the datum carriers used by `Section4.R43.Trilinear`.
The coordinate derivative carrier is the angular Riesz multiplier, with the
symbol definition reused verbatim from R43.
-/

noncomputable section

open Set MeasureTheory FourierTransform NavierStokes.ProblemStatement
open EulerLpTranslation
open NSFormalization.Paper3
open NSFormalization.Source.RealSobolev
open NSFormalization.Section4.D01
open NSFormalization.Section4.D01.Homogeneous
open scoped ENNReal SchwartzMap LineDeriv ComplexConjugate ContDiff

namespace NSFormalization.Section4.A05

abbrev derivativeSymbol (j : Fin 3) (ξ : Space) : ℂ :=
  NSFormalization.Section4.R43.rieszCoordinateSymbol j ξ

theorem derivativeSymbol_measurable (j : Fin 3) : Measurable (derivativeSymbol j) := by
  unfold derivativeSymbol NSFormalization.Section4.R43.rieszCoordinateSymbol
  apply Measurable.ite (measurableSet_singleton (0 : Space)) measurable_const
  exact measurable_const.mul (Complex.measurable_ofReal.comp
    ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) j).measurable.div
      continuous_norm.measurable))

theorem derivativeSymbol_memLp (j : Fin 3) :
    MemLp (derivativeSymbol j) ⊤ (volume : Measure Space) :=
  memLp_top_of_bound (derivativeSymbol_measurable j).aestronglyMeasurable 1
    (Filter.Eventually.of_forall
      (NSFormalization.Section4.R43.rieszCoordinateSymbol_norm_le j))

def derivativeSymbolLp (j : Fin 3) : Lp ℂ ⊤ (volume : Measure Space) :=
  (derivativeSymbol_memLp j).toLp (derivativeSymbol j)

theorem derivativeSymbolLp_ae (j : Fin 3) :
    (derivativeSymbolLp j : Space → ℂ) =ᵐ[volume] derivativeSymbol j :=
  (derivativeSymbol_memLp j).coeFn_toLp

theorem derivativeSymbol_conj_neg (j : Fin 3) (ξ : Space) :
    conj (derivativeSymbol j (-ξ)) = derivativeSymbol j ξ := by
  by_cases hξ : ξ = 0
  · subst ξ
    simp [derivativeSymbol, NSFormalization.Section4.R43.rieszCoordinateSymbol]
  · have hnξ : -ξ ≠ 0 := neg_ne_zero.mpr hξ
    simp only [derivativeSymbol, NSFormalization.Section4.R43.rieszCoordinateSymbol,
      hξ, hnξ, ite_false, norm_neg, PiLp.neg_apply,
      map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring

/-! ## The bounded physical Riesz transform -/

def rieszFrequencyL2 (j : Fin 3) : MNS2.R3L2Velocity →L[ℂ] MNS2.R3L2Velocity :=
  MNS2.r3L2ScalarMultiplier (derivativeSymbolLp j)

theorem rieszFrequencyL2_ae (j : Fin 3) (F : MNS2.R3L2Velocity) :
    (rieszFrequencyL2 j F : Space → MNS2.R3C) =ᵐ[volume]
      fun ξ => derivativeSymbol j ξ • F ξ := by
  let : ENNReal.HolderTriple (⊤ : ℝ≥0∞) (2 : ℝ≥0∞) (2 : ℝ≥0∞) := ⟨by simp⟩
  change ((derivativeSymbolLp j • F : MNS2.R3L2Velocity) : Space → MNS2.R3C) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) (derivativeSymbolLp j) F,
    derivativeSymbolLp_ae j] with ξ hmul hs
  rw [hmul, Pi.smul_apply', hs]

/-- The physical order-zero Riesz transform, on the complexified vector `L²` carrier. -/
def rieszPhysicalL2C (j : Fin 3) : MNS2.R3L2Velocity →L[ℂ] MNS2.R3L2Velocity :=
  fourierInvCLM ℂ MNS2.R3L2Velocity ∘L
    rieszFrequencyL2 j ∘L fourierCLM ℂ MNS2.R3L2Velocity

theorem fourier_rieszPhysicalL2C (j : Fin 3) (F : MNS2.R3L2Velocity) :
    FourierTransform.fourier (rieszPhysicalL2C j F) =
      rieszFrequencyL2 j (FourierTransform.fourier F) := by
  simp [rieszPhysicalL2C]

def translationPhase (a ξ : Space) : ℂ :=
  ((Real.fourierChar (inner ℝ a ξ) : Circle) : ℂ)

theorem translationPhase_continuous (a : Space) : Continuous (translationPhase a) := by
  exact continuous_subtype_val.comp
    (Real.continuous_fourierChar.comp (by fun_prop))

theorem translationPhase_norm (a ξ : Space) : ‖translationPhase a ξ‖ = 1 := by
  exact Circle.norm_coe _

def translationPhaseLp (a : Space) : Lp ℂ ⊤ (volume : Measure Space) :=
  (memLp_top_of_bound (translationPhase_continuous a).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ξ => le_of_eq (translationPhase_norm a ξ))).toLp
      (translationPhase a)

theorem translationPhaseLp_ae (a : Space) :
    (translationPhaseLp a : Space → ℂ) =ᵐ[volume] translationPhase a :=
  (memLp_top_of_bound (translationPhase_continuous a).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ξ => le_of_eq (translationPhase_norm a ξ))).coeFn_toLp

def translationPhaseMultiplier (a : Space) :
    MNS2.R3L2Velocity →L[ℂ] MNS2.R3L2Velocity :=
  MNS2.r3L2ScalarMultiplier (translationPhaseLp a)

theorem translationPhaseMultiplier_ae (a : Space) (F : MNS2.R3L2Velocity) :
    (translationPhaseMultiplier a F : Space → MNS2.R3C) =ᵐ[volume]
      fun ξ => translationPhase a ξ • F ξ := by
  let : ENNReal.HolderTriple (⊤ : ℝ≥0∞) (2 : ℝ≥0∞) (2 : ℝ≥0∞) := ⟨by simp⟩
  change ((translationPhaseLp a • F : MNS2.R3L2Velocity) : Space → MNS2.R3C) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) (translationPhaseLp a) F,
    translationPhaseLp_ae a] with ξ hmul hs
  rw [hmul, Pi.smul_apply', hs]

theorem fourier_translation (a : Space) (F : MNS2.R3L2Velocity) :
    FourierTransform.fourier (EulerLpTranslation.translation a F) =
      translationPhaseMultiplier a (FourierTransform.fourier F) := by
  let P := fun F : MNS2.R3L2Velocity =>
    FourierTransform.fourier (EulerLpTranslation.translation a F) =
      translationPhaseMultiplier a (FourierTransform.fourier F)
  apply DenseRange.induction_on (p := P)
    (SchwartzMap.denseRange_toLpCLM (E := Space) (F := MNS2.R3C)
      (p := 2) (μ := volume) ENNReal.ofNat_ne_top) F
  · apply isClosed_eq
    · exact continuous_fourier.comp
        (EulerLpTranslation.translation a).toContinuousLinearMap.continuous
    · exact (translationPhaseMultiplier a).continuous.comp continuous_fourier
  · intro φ
    let τ : SchwartzMap Space MNS2.R3C := φ.compSubConstCLM ℂ (-a)
    have htrans : EulerLpTranslation.translation a (φ.toLp 2 volume) =
        τ.toLp 2 volume := by
      apply Lp.ext
      filter_upwards [EulerLpTranslation.translation_ae a (φ.toLp 2 volume),
        (measurePreserving_add_right (volume : Measure Space) a).quasiMeasurePreserving.ae
          (φ.coeFn_toLp 2 volume), τ.coeFn_toLp 2 volume] with x htr hφ hτ
      rw [htr, hφ, hτ]
      simp [τ]
    change FourierTransform.fourier
        (EulerLpTranslation.translation a (φ.toLp 2 volume)) =
      translationPhaseMultiplier a (FourierTransform.fourier (φ.toLp 2 volume))
    rw [htrans, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
    apply Lp.ext
    filter_upwards [(FourierTransform.fourier τ).coeFn_toLp 2 volume,
      translationPhaseMultiplier_ae a ((FourierTransform.fourier φ).toLp 2 volume),
      (FourierTransform.fourier φ).coeFn_toLp 2 volume] with ξ hleft hright hφ
    rw [hleft, hright, hφ]
    rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
    have hτfun : (τ : Space → MNS2.R3C) = fun x => φ (x + a) := by
      funext x
      simp [τ]
    rw [hτfun]
    have h := congrFun (VectorFourier.fourierIntegral_comp_add_right
      Real.fourierChar volume (innerₗ Space) (φ : Space → MNS2.R3C) a) ξ
    change VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ Space)
        ((φ : Space → MNS2.R3C) ∘ fun x : Space => x + a) ξ =
      translationPhase a ξ •
        VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ Space)
          (φ : Space → MNS2.R3C) ξ
    simpa only [innerₗ_apply_apply, translationPhase,
      Circle.smul_def] using h

theorem rieszPhysicalL2C_translation (j : Fin 3) (a : Space)
    (F : MNS2.R3L2Velocity) :
    rieszPhysicalL2C j (EulerLpTranslation.translation a F) =
      EulerLpTranslation.translation a (rieszPhysicalL2C j F) := by
  apply (Lp.fourierTransformₗᵢ Space MNS2.R3C).injective
  change FourierTransform.fourier
      (rieszPhysicalL2C j (EulerLpTranslation.translation a F)) =
    FourierTransform.fourier
      (EulerLpTranslation.translation a (rieszPhysicalL2C j F))
  rw [fourier_rieszPhysicalL2C, fourier_translation,
    fourier_translation, fourier_rieszPhysicalL2C]
  apply Lp.ext
  filter_upwards [rieszFrequencyL2_ae j
      (translationPhaseMultiplier a (FourierTransform.fourier F)),
    translationPhaseMultiplier_ae a (FourierTransform.fourier F),
    translationPhaseMultiplier_ae a
      (rieszFrequencyL2 j (FourierTransform.fourier F)),
    rieszFrequencyL2_ae j (FourierTransform.fourier F)] with ξ h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄, smul_smul, smul_smul]
  congr 1
  exact mul_comm _ _

def complexifyFiber : Space →L[ℝ] MNS2.R3C :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      Complex.ofRealCLM.comp (EuclideanSpace.proj i))

def complexifyLp : EulerLpTranslation.L2Space Space →L[ℝ] MNS2.R3L2Velocity :=
  complexifyFiber.compLpL 2 volume

def realifyFiber : MNS2.R3C →L[ℝ] Space :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      Complex.reCLM.comp (PiLp.proj 2 (fun _ : Fin 3 => ℂ) i))

def realifyLp : MNS2.R3L2Velocity →L[ℝ] EulerLpTranslation.L2Space Space :=
  realifyFiber.compLpL 2 volume

theorem complexifyFiber_apply (x : Space) :
    complexifyFiber x = WithLp.toLp 2 (fun i => ((x i : ℝ) : ℂ)) := by
  ext i
  rfl

theorem realifyFiber_complexifyFiber (x : Space) :
    realifyFiber (complexifyFiber x) = x := by
  ext i
  rfl

theorem complexifyLp_ae (F : EulerLpTranslation.L2Space Space) :
    (complexifyLp F : Space → MNS2.R3C) =ᵐ[volume]
      fun x => complexifyFiber (F x) :=
  complexifyFiber.coeFn_compLpL F

theorem realifyLp_ae (F : MNS2.R3L2Velocity) :
    (realifyLp F : Space → Space) =ᵐ[volume]
      fun x => realifyFiber (F x) :=
  realifyFiber.coeFn_compLpL F

theorem realifyLp_complexifyLp (F : EulerLpTranslation.L2Space Space) :
    realifyLp (complexifyLp F) = F := by
  apply Lp.ext
  filter_upwards [realifyLp_ae (complexifyLp F), complexifyLp_ae F] with x hr hc
  rw [hr, hc, realifyFiber_complexifyFiber]

theorem complexifyLp_isReal (F : EulerLpTranslation.L2Space Space) :
    MNS2.IsR3RealVelocity (complexifyLp F) := by
  unfold MNS2.IsR3RealVelocity
  apply Lp.ext
  filter_upwards [MNS2.coeFn_r3L2Conj (complexifyLp F), complexifyLp_ae F] with x hc hF
  rw [hc, hF]
  ext i
  simp [complexifyFiber_apply]

theorem complexifyLp_realifyLp_of_isReal {F : MNS2.R3L2Velocity}
    (hF : MNS2.IsR3RealVelocity F) : complexifyLp (realifyLp F) = F := by
  have hconj := MNS2.coeFn_r3L2Conj F
  unfold MNS2.IsR3RealVelocity at hF
  rw [hF] at hconj
  apply Lp.ext
  filter_upwards [complexifyLp_ae (realifyLp F), realifyLp_ae F, hconj]
    with x hc hr hreal
  rw [hc, hr]
  ext i
  have hi := congrArg (fun z : MNS2.R3C => z i) hreal
  change ((F x i).re : ℂ) = F x i
  apply Complex.ext
  · simp
  · have him := congrArg Complex.im hi
    simp only [MNS2.r3CConj_apply, Complex.conj_im] at him
    simp only [Complex.ofReal_im]
    linarith

theorem complexifyLp_translation (a : Space) (F : EulerLpTranslation.L2Space Space) :
    complexifyLp (EulerLpTranslation.translation a F) =
      EulerLpTranslation.translation a (complexifyLp F) := by
  apply Lp.ext
  filter_upwards [complexifyLp_ae (EulerLpTranslation.translation a F),
    EulerLpTranslation.translation_ae a F,
    EulerLpTranslation.translation_ae a (complexifyLp F),
    (measurePreserving_add_right (volume : Measure Space) a).quasiMeasurePreserving.ae
      (complexifyLp_ae F)] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]

theorem realifyLp_translation (a : Space) (F : MNS2.R3L2Velocity) :
    realifyLp (EulerLpTranslation.translation a F) =
      EulerLpTranslation.translation a (realifyLp F) := by
  apply Lp.ext
  filter_upwards [realifyLp_ae (EulerLpTranslation.translation a F),
    EulerLpTranslation.translation_ae a F,
    EulerLpTranslation.translation_ae a (realifyLp F),
    (measurePreserving_add_right (volume : Measure Space) a).quasiMeasurePreserving.ae
      (realifyLp_ae F)] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]

theorem conjugateSymmetric_ae {F : MNS2.R3L2Velocity}
    (hF : MNS2.IsR3ConjugateSymmetricVelocity F) :
    (fun ξ => MNS2.r3CConj (F (-ξ))) =ᵐ[volume] (F : Space → MNS2.R3C) := by
  unfold MNS2.IsR3ConjugateSymmetricVelocity at hF
  have hreflect := MNS2.coeFn_r3L2Reflect (MNS2.r3L2Conj F)
  rw [hF] at hreflect
  have hconj := (Measure.measurePreserving_neg
    (volume : Measure Space)).quasiMeasurePreserving.ae (MNS2.coeFn_r3L2Conj F)
  filter_upwards [hreflect, hconj] with ξ hr hc
  rw [hr, hc]

theorem rieszFrequencyL2_conjugateSymmetric (j : Fin 3) {F : MNS2.R3L2Velocity}
    (hF : MNS2.IsR3ConjugateSymmetricVelocity F) :
    MNS2.IsR3ConjugateSymmetricVelocity (rieszFrequencyL2 j F) := by
  unfold MNS2.IsR3ConjugateSymmetricVelocity
  apply Lp.ext
  have hneg := (Measure.measurePreserving_neg
    (volume : Measure Space)).quasiMeasurePreserving.ae (rieszFrequencyL2_ae j F)
  have hconj := (Measure.measurePreserving_neg
    (volume : Measure Space)).quasiMeasurePreserving.ae
      (MNS2.coeFn_r3L2Conj (rieszFrequencyL2 j F))
  filter_upwards [MNS2.coeFn_r3L2Reflect
      (MNS2.r3L2Conj (rieszFrequencyL2 j F)), hconj, hneg,
    conjugateSymmetric_ae hF, rieszFrequencyL2_ae j F]
      with ξ href hconj hneg hreal hhere
  rw [href, hconj, hneg, MNS2.r3CConj_smul,
    derivativeSymbol_conj_neg, hreal, hhere]

theorem rieszPhysicalL2C_isReal (j : Fin 3) {F : MNS2.R3L2Velocity}
    (hF : MNS2.IsR3RealVelocity F) :
    MNS2.IsR3RealVelocity (rieszPhysicalL2C j F) := by
  apply (MNS2.isR3RealVelocity_iff_fourier_conjugateSymmetric _).2
  rw [fourier_rieszPhysicalL2C]
  exact rieszFrequencyL2_conjugateSymmetric j
    ((MNS2.isR3RealVelocity_iff_fourier_conjugateSymmetric F).1 hF)

def rieszPhysicalL2 (j : Fin 3) :
    EulerLpTranslation.L2Space Space →L[ℝ] EulerLpTranslation.L2Space Space :=
  realifyLp.comp ((rieszPhysicalL2C j).restrictScalars ℝ |>.comp complexifyLp)

theorem complexifyLp_rieszPhysicalL2 (j : Fin 3)
    (F : EulerLpTranslation.L2Space Space) :
    complexifyLp (rieszPhysicalL2 j F) = rieszPhysicalL2C j (complexifyLp F) := by
  exact complexifyLp_realifyLp_of_isReal
    (rieszPhysicalL2C_isReal j (complexifyLp_isReal F))

theorem rieszPhysicalL2_translation (j : Fin 3) (a : Space)
    (F : EulerLpTranslation.L2Space Space) :
    rieszPhysicalL2 j (EulerLpTranslation.translation a F) =
      EulerLpTranslation.translation a (rieszPhysicalL2 j F) := by
  have hinj : Function.Injective complexifyLp := by
    intro X Y hXY
    have := congrArg realifyLp hXY
    simpa only [realifyLp_complexifyLp] using this
  apply hinj
  rw [complexifyLp_rieszPhysicalL2, complexifyLp_translation,
    rieszPhysicalL2C_translation, complexifyLp_translation,
    complexifyLp_rieszPhysicalL2]

theorem coordinates_fourier (F : MNS2.R3L2Velocity) (i : Fin 3) :
    NSFormalization.Source.FiniteHilbertBochner.coordinates 2 volume
        (FourierTransform.fourier F) i =
      FourierTransform.fourier
        (NSFormalization.Source.FiniteHilbertBochner.coordinates 2 volume F i) := by
  let P := fun F : MNS2.R3L2Velocity =>
    NSFormalization.Source.FiniteHilbertBochner.coordinates 2 volume
        (FourierTransform.fourier F) i =
      FourierTransform.fourier
        (NSFormalization.Source.FiniteHilbertBochner.coordinates 2 volume F i)
  apply DenseRange.induction_on (p := P)
    (SchwartzMap.denseRange_toLpCLM (E := Space) (F := MNS2.R3C)
      (p := 2) (μ := volume) ENNReal.ofNat_ne_top) F
  · apply isClosed_eq
    · exact
        (NSFormalization.Source.FiniteHilbertBochner.coord (H := ℂ) i |>.compLpL 2 volume).continuous.comp
          continuous_fourier
    · exact continuous_fourier.comp
        (NSFormalization.Source.FiniteHilbertBochner.coord (H := ℂ) i |>.compLpL 2 volume).continuous
  · intro φ
    change NSFormalization.Source.FiniteHilbertBochner.coordinates 2 volume
        (FourierTransform.fourier (φ.toLp 2 volume)) i =
      FourierTransform.fourier
        (NSFormalization.Source.FiniteHilbertBochner.coordinates 2 volume
          (φ.toLp 2 volume) i)
    rw [SchwartzMap.toLp_fourier_eq]
    have hcoord (g : SchwartzMap Space MNS2.R3C) :
        NSFormalization.Source.FiniteHilbertBochner.coordinates 2 volume
            (g.toLp 2 volume) i =
          (MNS2.r3SchwartzCoordinate i g).toLp 2 volume := by
      apply Lp.ext
      filter_upwards [NSFormalization.Section4.D01.Leray.coordinates_ae
          volume (g.toLp 2 volume) i, g.coeFn_toLp 2 volume,
        (MNS2.r3SchwartzCoordinate i g).coeFn_toLp 2 volume] with x h₁ h₂ h₃
      rw [h₁, h₂, h₃]
      rfl
    rw [hcoord, hcoord, SchwartzMap.toLp_fourier_eq,
      MNS2.fourier_r3SchwartzCoordinate_eq]

theorem componentLp_smoothField (A : SmoothL2Field Space) (i : Fin 3) :
    componentLp A.memLp i =
      NSFormalization.Source.FiniteHilbertBochner.coordinates 2 volume
        (complexifyLp A.toLp) i := by
  apply Lp.ext
  filter_upwards [componentLp_ae A.memLp i,
    NSFormalization.Section4.D01.Leray.coordinates_ae volume (complexifyLp A.toLp) i,
    complexifyLp_ae A.toLp, A.toLp_ae] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]
  rfl

theorem fourier_directionalField_component_ae (A : SmoothL2Field Space)
    (j i : Fin 3) :
    ((NSFormalization.Source.FiniteHilbertBochner.coordinates 2 volume
        (FourierTransform.fourier
          (complexifyLp (A.directionalField (coordinateVector j)).toLp)) i : FourierData) :
      Space → ℂ) =ᵐ[volume]
      fun ξ => (2 * (Real.pi : ℂ) * Complex.I) * ((ξ j : ℝ) : ℂ) *
        (NSFormalization.Source.FiniteHilbertBochner.coordinates 2 volume
          (FourierTransform.fourier (complexifyLp A.toLp)) i) ξ := by
  have hdb := db_cycles_full (s := 0) j
    (isSobolevDatum_orderZeroDatum A.memLp)
    (isSobolevDatum_orderZeroDatum
      (A.directionalField (coordinateVector j)).memLp)
    (fun k ψ => smoothField_weakDeriv_pairing A j k ψ) i
  rw [NSFormalization.Section4.D01.orderZeroDatum_coe,
    NSFormalization.Section4.D01.orderZeroDatum_coe,
    ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply,
    componentLp_smoothField, componentLp_smoothField,
    ← coordinates_fourier, ← coordinates_fourier] at hdb
  exact Filter.EventuallyEq.symm hdb

def sourceSmoothField (v : SpatialField)
    (hv : NSFormalization.Section4.A02.MemHInfty v) : SmoothL2Field Space :=
  ⟨v, hv.1, memHInfty_jets hv.1 hv.2⟩

/-- The actual `L²` class of `Λv`, realized as `-∑ⱼ Rⱼ ∂ⱼv`. -/
def rieszLambdaL2 (v : SpatialField)
    (hv : NSFormalization.Section4.A02.MemHInfty v) :
    EulerLpTranslation.L2Space Space :=
  -∑ j : Fin 3, rieszPhysicalL2 j
    ((sourceSmoothField v hv).directionalField (coordinateVector j)).toLp

theorem rieszLambdaL2_smoothOrbit (v : SpatialField)
    (hv : NSFormalization.Section4.A02.MemHInfty v) :
    EulerMeanSmoothRepresentative.SmoothOrbit (rieszLambdaL2 v hv) := by
  let A := sourceSmoothField v hv
  have heq :
      (fun a : Space => EulerLpTranslation.translation a (rieszLambdaL2 v hv)) =
        fun a => -∑ j : Fin 3, rieszPhysicalL2 j
          (EulerLpTranslation.translation a
            ((A.directionalField (coordinateVector j)).toLp)) := by
    funext a
    simp only [rieszLambdaL2, A, map_neg, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    exact rieszPhysicalL2_translation j a _ |>.symm
  change ContDiff ℝ ∞
    (fun a : Space => EulerLpTranslation.translation a (rieszLambdaL2 v hv))
  rw [heq]
  exact (ContDiff.sum fun j (_ : j ∈ Finset.univ) =>
    (rieszPhysicalL2 j).contDiff.comp
      (A.directionalField (coordinateVector j)).translation_contDiff).neg

/-- U4: the literal smooth physical representative of the `L²` class with
Fourier transform `|ξ| · v̂` in angular frequency. -/
def rieszLambda (v : SpatialField)
    (hv : NSFormalization.Section4.A02.MemHInfty v) : SpatialField :=
  (EulerMeanSmoothRepresentative.smoothL2Field
    (rieszLambdaL2 v hv) (rieszLambdaL2_smoothOrbit v hv)).field

theorem rieszLambda_toLp (v : SpatialField)
    (hv : NSFormalization.Section4.A02.MemHInfty v) :
    (EulerMeanSmoothRepresentative.smoothL2Field
      (rieszLambdaL2 v hv) (rieszLambdaL2_smoothOrbit v hv)).toLp =
        rieszLambdaL2 v hv :=
  EulerMeanSmoothRepresentative.smoothL2Field_toLp _ _

/-- The square-integrability witness carried by the canonical smooth
representative of `rieszLambdaL2`. -/
theorem rieszLambdaMemLp (v : SpatialField)
    (hv : NSFormalization.Section4.A02.MemHInfty v) :
    MemLp (rieszLambda v hv) 2 volume :=
  (EulerMeanSmoothRepresentative.smoothL2Field
    (rieszLambdaL2 v hv) (rieszLambdaL2_smoothOrbit v hv)).memLp

/-- U4 regularity: bounded Riesz transforms preserve the smooth translation
orbit, and the canonical representative has square-integrable jets of every order. -/
theorem rieszLambda_memHInfty (v : SpatialField)
    (hv : NSFormalization.Section4.A02.MemHInfty v) :
    NSFormalization.Section4.A02.MemHInfty (rieszLambda v hv) := by
  let L := EulerMeanSmoothRepresentative.smoothL2Field
    (rieszLambdaL2 v hv) (rieszLambdaL2_smoothOrbit v hv)
  exact memHInfty_of_contDiff_memLp L.smooth L.integrable

theorem riesz_symbol_derivative_sum (ξ : Space) :
    -(∑ j : Fin 3, derivativeSymbol j ξ *
        ((2 * (Real.pi : ℂ) * Complex.I) * ((ξ j : ℝ) : ℂ))) =
      ((NSFormalization.Source.frequencyUnit * ‖ξ‖ : ℝ) : ℂ) := by
  by_cases hξ : ξ = 0
  · subst ξ
    simp [derivativeSymbol, NSFormalization.Section4.R43.rieszCoordinateSymbol]
  · have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
    have hsq : ‖ξ‖ ^ 2 = ∑ j : Fin 3, (ξ j) ^ 2 := by
      simpa [Real.norm_eq_abs, sq_abs] using
        (PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) ξ)
    simp only [derivativeSymbol, NSFormalization.Section4.R43.rieszCoordinateSymbol,
      hξ, ite_false, Fin.sum_univ_three, NSFormalization.Source.frequencyUnit]
    push_cast
    field_simp [hn]
    rw [Complex.I_sq, neg_one_mul, neg_neg]
    rw [Fin.sum_univ_three] at hsq
    exact_mod_cast hsq.symm

theorem fourier_rieszLambdaL2_component_ae (v : SpatialField)
    (hv : NSFormalization.Section4.A02.MemHInfty v) (i : Fin 3) :
    ((NSFormalization.Source.FiniteHilbertBochner.coordinates 2 volume
        (FourierTransform.fourier (complexifyLp (rieszLambdaL2 v hv))) i : FourierData) :
      Space → ℂ) =ᵐ[volume]
      fun ξ => ((NSFormalization.Source.frequencyUnit * ‖ξ‖ : ℝ) : ℂ) *
        (NSFormalization.Source.FiniteHilbertBochner.coordinates 2 volume
          (FourierTransform.fourier (complexifyLp (sourceSmoothField v hv).toLp)) i) ξ := by
  let A := sourceSmoothField v hv
  have hfourier : FourierTransform.fourier (complexifyLp (rieszLambdaL2 v hv)) =
      -∑ j : Fin 3, rieszFrequencyL2 j
        (FourierTransform.fourier
          (complexifyLp (A.directionalField (coordinateVector j)).toLp)) := by
    calc
      _ = FourierTransform.fourier
          (-∑ j : Fin 3, rieszPhysicalL2C j
            (complexifyLp (A.directionalField (coordinateVector j)).toLp)) := by
            congr 1
            simp only [rieszLambdaL2, A, map_neg, map_sum,
              complexifyLp_rieszPhysicalL2]
      _ = -∑ j : Fin 3, FourierTransform.fourier
          (rieszPhysicalL2C j
            (complexifyLp (A.directionalField (coordinateVector j)).toLp)) := by
            change (fourierCLM ℂ MNS2.R3L2Velocity)
              (-∑ j : Fin 3, rieszPhysicalL2C j
                (complexifyLp (A.directionalField (coordinateVector j)).toLp)) =
              -∑ j : Fin 3, (fourierCLM ℂ MNS2.R3L2Velocity)
                (rieszPhysicalL2C j
                  (complexifyLp (A.directionalField (coordinateVector j)).toLp))
            rw [map_neg, map_sum]
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        exact fourier_rieszPhysicalL2C j _
  rw [hfourier]
  have hcoord :
      NSFormalization.Source.FiniteHilbertBochner.coordinates 2 volume
          (-∑ j : Fin 3, rieszFrequencyL2 j
            (FourierTransform.fourier
              (complexifyLp (A.directionalField (coordinateVector j)).toLp))) i =
        -∑ j : Fin 3,
          NSFormalization.Source.FiniteHilbertBochner.coordinates 2 volume
            (rieszFrequencyL2 j
              (FourierTransform.fourier
                (complexifyLp (A.directionalField (coordinateVector j)).toLp))) i := by
    simp only [NSFormalization.Source.FiniteHilbertBochner.coordinates, map_neg, map_sum]
  rw [hcoord]
  have hriesz : ∀ᵐ ξ : Space ∂volume, ∀ j : Fin 3,
      (NSFormalization.Source.FiniteHilbertBochner.coordinates 2 volume
        (rieszFrequencyL2 j
          (FourierTransform.fourier
            (complexifyLp (A.directionalField (coordinateVector j)).toLp))) i) ξ =
        derivativeSymbol j ξ *
          (NSFormalization.Source.FiniteHilbertBochner.coordinates 2 volume
            (FourierTransform.fourier
              (complexifyLp (A.directionalField (coordinateVector j)).toLp)) i) ξ := by
    rw [ae_all_iff]
    intro j
    filter_upwards [NSFormalization.Section4.D01.Leray.coordinates_ae volume
        (rieszFrequencyL2 j
          (FourierTransform.fourier
            (complexifyLp (A.directionalField (coordinateVector j)).toLp))) i,
      rieszFrequencyL2_ae j
        (FourierTransform.fourier
          (complexifyLp (A.directionalField (coordinateVector j)).toLp)),
      NSFormalization.Section4.D01.Leray.coordinates_ae volume
        (FourierTransform.fourier
          (complexifyLp (A.directionalField (coordinateVector j)).toLp)) i]
      with ξ h₁ h₂ h₃
    rw [h₁, h₂, h₃]
    rfl
  have hderiv : ∀ᵐ ξ : Space ∂volume, ∀ j : Fin 3,
      (NSFormalization.Source.FiniteHilbertBochner.coordinates 2 volume
        (FourierTransform.fourier
          (complexifyLp (A.directionalField (coordinateVector j)).toLp)) i) ξ =
        (2 * (Real.pi : ℂ) * Complex.I) * ((ξ j : ℝ) : ℂ) *
          (NSFormalization.Source.FiniteHilbertBochner.coordinates 2 volume
            (FourierTransform.fourier (complexifyLp A.toLp)) i) ξ := by
    rw [ae_all_iff]
    exact fun j => fourier_directionalField_component_ae A j i
  filter_upwards [Lp.coeFn_neg (∑ j : Fin 3,
      NSFormalization.Source.FiniteHilbertBochner.coordinates 2 volume
        (rieszFrequencyL2 j
          (FourierTransform.fourier
            (complexifyLp (A.directionalField (coordinateVector j)).toLp))) i),
    Lp.coeFn_finsetSum Finset.univ (fun j : Fin 3 =>
      NSFormalization.Source.FiniteHilbertBochner.coordinates 2 volume
        (rieszFrequencyL2 j
          (FourierTransform.fourier
            (complexifyLp (A.directionalField (coordinateVector j)).toLp))) i),
    hriesz, hderiv] with ξ hneg hsum hr hd
  rw [hneg]
  simp only [Pi.neg_apply]
  rw [hsum]
  simp only [Finset.sum_apply]
  rw [Finset.sum_congr rfl (fun j _ => by rw [hr j, hd j])]
  have hfactor :
      -∑ j : Fin 3, derivativeSymbol j ξ *
          ((2 * (Real.pi : ℂ) * Complex.I) * ((ξ j : ℝ) : ℂ) *
            (NSFormalization.Source.FiniteHilbertBochner.coordinates 2 volume
              (FourierTransform.fourier (complexifyLp A.toLp)) i) ξ) =
        (-(∑ j : Fin 3, derivativeSymbol j ξ *
          ((2 * (Real.pi : ℂ) * Complex.I) * ((ξ j : ℝ) : ℂ)))) *
            (NSFormalization.Source.FiniteHilbertBochner.coordinates 2 volume
              (FourierTransform.fourier (complexifyLp A.toLp)) i) ξ := by
    simp only [Fin.sum_univ_three]
    ring
  rw [hfactor]
  simpa only [A] using congrArg
    (fun c : ℂ => c *
      (NSFormalization.Source.FiniteHilbertBochner.coordinates 2 volume
        (FourierTransform.fourier (complexifyLp A.toLp)) i) ξ)
    (riesz_symbol_derivative_sum ξ)

/-! ## The angular Fourier identity for the physical realization -/

/-- The angular Fourier transform of an `L²` function is represented by the
normalized dilation of its Mathlib `L²` Fourier transform. -/
theorem angularFourierDistribution_lp (g : FourierData) :
    angularFourierDistribution (g : TemperedDistribution Space ℂ) =
      (angularFrequencyDilation (FourierTransform.fourier g) :
        TemperedDistribution Space ℂ) := by
  change angularDistributionDilation
      (FourierTransform.fourier (g : TemperedDistribution Space ℂ)) = _
  rw [Lp.fourier_toTemperedDistribution_eq,
    ← angularFrequencyDilation_toDistribution]

/-- The componentwise `L²` classes of a square-integrable real vector field
form its canonical slice distribution. -/
theorem isSliceDistribution_componentLp {z : SpatialField}
    (hz : MemLp z 2 volume) :
    IsSliceDistribution z
      (fun i => (componentLp hz i : TemperedDistribution Space ℂ)) := by
  intro i ψ
  rw [Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [componentLp_ae hz i] with x hx
  rw [hx, smul_eq_mul]

/-- A homogeneous datum identifies the actual angular `L²` Fourier function
of an `L²` physical representative.  The proof uses locally-integrable
uniqueness, so it is valid at the order-`3/2` endpoint as well. -/
theorem homogeneousDatum_angularFourier_ae {s : ℝ} {G g : FourierData}
    (hG : IsHomogeneousDatum s G (g : TemperedDistribution Space ℂ)) :
    (angularFrequencyDilation (FourierTransform.fourier g) : Space → ℂ) =ᵐ[volume]
      fun ξ => ((‖ξ‖ ^ (-s) : ℝ) : ℂ) * G ξ := by
  let A : FourierData := angularFrequencyDilation (FourierTransform.fourier g)
  let W : Space → ℂ := fun ξ => ((‖ξ‖ ^ (-s) : ℝ) : ℂ) * G ξ
  have hangular : angularFourierDistribution (g : TemperedDistribution Space ℂ) =
      (A : TemperedDistribution Space ℂ) := by
    simpa only [A] using angularFourierDistribution_lp g
  have hWloc : LocallyIntegrable W (volume : Measure Space) :=
    locallyIntegrable_of_schwartz_mul (fun ψ => by
      simpa only [W] using (hG ψ).1)
  have hAloc : LocallyIntegrable (A : Space → ℂ) (volume : Measure Space) :=
    (Lp.memLp A).locallyIntegrable (by norm_num)
  have hzero : ∀ ψ : SchwartzMap Space ℂ,
      (∫ ξ : Space, ((A : Space → ℂ) ξ - W ξ) * ψ ξ) = 0 := by
    intro ψ
    have hAint : Integrable (fun ξ : Space => ψ ξ * (A : Space → ℂ) ξ) := by
      change Integrable ((ψ : Space → ℂ) * (A : Space → ℂ))
      exact (ψ.memLp 2 volume).integrable_mul (Lp.memLp A)
    have hp := congrArg (fun U : TemperedDistribution Space ℂ => U ψ) hangular
    rw [Lp.toTemperedDistribution_apply] at hp
    have hp' : angularFourierDistribution (g : TemperedDistribution Space ℂ) ψ =
        ∫ ξ : Space, ψ ξ * (A : Space → ℂ) ξ := by
      simpa only [smul_eq_mul] using hp
    rw [show (fun ξ : Space => ((A : Space → ℂ) ξ - W ξ) * ψ ξ) =
        fun ξ => ψ ξ * (A : Space → ℂ) ξ - ψ ξ * W ξ by
          funext ξ; ring,
      integral_sub hAint (by simpa only [W] using (hG ψ).1),
      ← hp', ← (hG ψ).2, sub_self]
  have hae :=
    NavierStokesR3.WeakFourierUniqueness.ae_eq_zero_of_integral_schwartz_test_mul_eq_zero
      (fun ξ : Space => (A : Space → ℂ) ξ - W ξ) (hAloc.sub hWloc) hzero
  filter_upwards [hae] with ξ hξ
  exact sub_eq_zero.mp hξ

/-- The cycles-frequency component formula above, rewritten using the
canonical scalar `L²` classes of the two literal real fields. -/
theorem fourier_rieszLambda_component_ae (v : SpatialField)
    (hv : NSFormalization.Section4.A02.MemHInfty v) (i : Fin 3) :
    ((FourierTransform.fourier
        (componentLp (rieszLambdaMemLp v hv) i) : FourierData) : Space → ℂ)
      =ᵐ[volume]
      fun ξ => ((NSFormalization.Source.frequencyUnit * ‖ξ‖ : ℝ) : ℂ) *
        (FourierTransform.fourier
          (componentLp (sourceSmoothField v hv).memLp i) : FourierData) ξ := by
  let L := EulerMeanSmoothRepresentative.smoothL2Field
    (rieszLambdaL2 v hv) (rieszLambdaL2_smoothOrbit v hv)
  have h := fourier_rieszLambdaL2_component_ae v hv i
  have hL : componentLp (rieszLambdaMemLp v hv) i =
      NSFormalization.Source.FiniteHilbertBochner.coordinates 2 volume
        (complexifyLp L.toLp) i := by
    change componentLp L.memLp i = _
    exact componentLp_smoothField L i
  have hV := componentLp_smoothField (sourceSmoothField v hv) i
  rw [hL, hV, ← coordinates_fourier, ← coordinates_fourier]
  simpa only [L, EulerMeanSmoothRepresentative.smoothL2Field_toLp] using h

/-- After normalized angular dilation the cycles multiplier
`frequencyUnit * ‖ξ‖` is exactly the manuscript multiplier `‖ξ‖`. -/
theorem angular_rieszLambda_component_ae (v : SpatialField)
    (hv : NSFormalization.Section4.A02.MemHInfty v) (i : Fin 3) :
    (angularFrequencyDilation
        (FourierTransform.fourier
          (componentLp (rieszLambdaMemLp v hv) i)) : Space → ℂ)
      =ᵐ[volume]
      fun ξ => ((‖ξ‖ : ℝ) : ℂ) *
        (angularFrequencyDilation
          (FourierTransform.fourier
            (componentLp (sourceSmoothField v hv).memLp i)) : FourierData) ξ := by
  have hqmp : Measure.QuasiMeasurePreserving
      (fun ξ : Space => NSFormalization.Source.frequencyUnit⁻¹ • ξ) volume volume := by
    refine ⟨(continuous_const_smul _).measurable, ?_⟩
    rw [Measure.map_addHaar_smul volume
      (inv_ne_zero NSFormalization.Source.frequencyUnit_pos.ne')]
    exact Measure.smul_absolutelyContinuous
  have hraw := hqmp.ae (fourier_rieszLambda_component_ae v hv i)
  have hL := NSFormalization.Paper3.angularFrequencyDilation_coeFn
    (FourierTransform.fourier
      (componentLp (rieszLambdaMemLp v hv) i))
  have hV := NSFormalization.Paper3.angularFrequencyDilation_coeFn
    (FourierTransform.fourier
      (componentLp (sourceSmoothField v hv).memLp i))
  filter_upwards [hL, hV, hraw] with ξ hLξ hVξ hrawξ
  rw [hLξ, hrawξ, hVξ]
  have hc : 0 < NSFormalization.Source.frequencyUnit :=
    NSFormalization.Source.frequencyUnit_pos
  have hnorm : NSFormalization.Source.frequencyUnit *
      ‖NSFormalization.Source.frequencyUnit⁻¹ • ξ‖ = ‖ξ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc),
      ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  rw [hnorm]
  simp only [Complex.real_smul]
  ring

/-- U4 datum identity: the physical field `rieszLambda v hv` has the supplied
order-`3/2` datum of `v` as its order-`1/2` datum.  In angular frequency this
is the equality `|ξ| · (|ξ|^{-3/2} Z) = |ξ|^{-1/2} Z`. -/
theorem rieszLambda_halfDatum (v : SpatialField)
    (hv : NSFormalization.Section4.A02.MemHInfty v)
    (Z : RealVectorSobolev (3 / 2))
    (hZ : IsHomogeneousSliceDatum (3 / 2) v Z) :
    IsHomogeneousSliceDatum (1 / 2) (rieszLambda v hv) Z := by
  obtain ⟨U, hU, hZU⟩ := hZ
  have hV : IsSliceDistribution v
      (fun i => (componentLp (sourceSmoothField v hv).memLp i :
        TemperedDistribution Space ℂ)) :=
    isSliceDistribution_componentLp (sourceSmoothField v hv).memLp
  have hUV := isSliceDistribution_unique hU hV
  subst U
  refine ⟨fun i => (componentLp (rieszLambdaMemLp v hv) i :
      TemperedDistribution Space ℂ),
    isSliceDistribution_componentLp (rieszLambdaMemLp v hv), ?_⟩
  intro i
  have hsource := homogeneousDatum_angularFourier_ae (hZU i)
  have hlambda := angular_rieszLambda_component_ae v hv i
  have hae :
      (angularFrequencyDilation
          (FourierTransform.fourier
            (componentLp (rieszLambdaMemLp v hv) i)) : Space → ℂ) =ᵐ[volume]
        fun ξ => ((‖ξ‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (Z i : FourierData) ξ := by
    filter_upwards [hlambda, hsource, volume.ae_ne (0 : Space)]
      with ξ hlam hsrc hξ
    rw [hlam, hsrc]
    have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    have hp : ‖ξ‖ * ‖ξ‖ ^ (-(3 / 2 : ℝ)) =
        ‖ξ‖ ^ (-(1 / 2 : ℝ)) := by
      calc
        ‖ξ‖ * ‖ξ‖ ^ (-(3 / 2 : ℝ)) =
            ‖ξ‖ ^ (1 : ℝ) * ‖ξ‖ ^ (-(3 / 2 : ℝ)) := by
              rw [Real.rpow_one]
        _ = ‖ξ‖ ^ ((1 : ℝ) + (-(3 / 2 : ℝ))) := by
              rw [Real.rpow_add hn]
        _ = ‖ξ‖ ^ (-(1 / 2 : ℝ)) := by norm_num
    rw [← mul_assoc, ← Complex.ofReal_mul, hp]
  intro φ
  have hLint : Integrable (fun ξ : Space => φ ξ *
      (angularFrequencyDilation
        (FourierTransform.fourier
          (componentLp (rieszLambdaMemLp v hv) i)) : FourierData) ξ) := by
    change Integrable ((φ : Space → ℂ) *
      (angularFrequencyDilation
        (FourierTransform.fourier
          (componentLp (rieszLambdaMemLp v hv) i)) : Space → ℂ))
    exact (φ.memLp 2 volume).integrable_mul (Lp.memLp _)
  have hprod : (fun ξ : Space => φ ξ *
      (angularFrequencyDilation
        (FourierTransform.fourier
          (componentLp (rieszLambdaMemLp v hv) i)) : FourierData) ξ) =ᵐ[volume]
      fun ξ => φ ξ *
        (((‖ξ‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (Z i : FourierData) ξ) := by
    filter_upwards [hae] with ξ hξ
    rw [hξ]
  refine ⟨hLint.congr hprod, ?_⟩
  rw [angularFourierDistribution_lp, Lp.toTemperedDistribution_apply]
  simpa only [smul_eq_mul] using integral_congr_ae hprod

def derivativeFourierDatum (j : Fin 3) (G : FourierData) : FourierData :=
  derivativeSymbolLp j • G

theorem derivativeFourierDatum_ae (j : Fin 3) (G : FourierData) :
    (derivativeFourierDatum j G : Space → ℂ) =ᵐ[volume]
      fun ξ => NSFormalization.Section4.R43.rieszCoordinateSymbol j ξ * G ξ := by
  filter_upwards [Lp.coeFn_lpSMul (r := 2) (derivativeSymbolLp j) G,
    derivativeSymbolLp_ae j] with ξ hmul hs
  change ((derivativeSymbolLp j • G : FourierData) : Space → ℂ) ξ = _
  rw [hmul]
  change (derivativeSymbolLp j : Space → ℂ) ξ * (G : Space → ℂ) ξ = _
  rw [hs]

theorem derivativeFourierDatum_realSymmetry (j : Fin 3) {G : FourierData}
    (hG : realSymmetry G = G) :
    realSymmetry (derivativeFourierDatum j G) = derivativeFourierDatum j G := by
  apply Lp.ext
  have hmulNeg := (Measure.measurePreserving_neg (volume : Measure Space)).quasiMeasurePreserving.ae
    (derivativeFourierDatum_ae j G)
  have hGreal := realSymmetry_ae G
  rw [hG] at hGreal
  filter_upwards [realSymmetry_ae (derivativeFourierDatum j G),
    derivativeFourierDatum_ae j G, hmulNeg, hGreal] with ξ hout hhere hneg hgr
  rw [hout, hneg, map_mul, derivativeSymbol_conj_neg, ← hgr, hhere]

def derivativeHalfComponent (j : Fin 3) (G : RealSobolevHilbert (3 / 2)) :
    RealSobolevHilbert (1 / 2) :=
  ⟨derivativeFourierDatum j (G : FourierData),
    (mem_realSubspace_iff (1 / 2) _).mpr
      (derivativeFourierDatum_realSymmetry j
        ((mem_realSubspace_iff (3 / 2) _).mp G.2))⟩

@[simp] theorem derivativeHalfComponent_coe (j : Fin 3)
    (G : RealSobolevHilbert (3 / 2)) :
    ((derivativeHalfComponent j G : RealSobolevHilbert (1 / 2)) : FourierData) =
      derivativeFourierDatum j (G : FourierData) := rfl

/-- The order-half datum obtained by applying one coordinate Riesz symbol to
each component of the order-three-halves datum. -/
def derivativeHalfDatum (j : Fin 3) (Z : RealVectorSobolev (3 / 2)) :
    RealVectorSobolev (1 / 2) :=
  WithLp.toLp 2 fun i => derivativeHalfComponent j (Z i)

theorem derivativeHalfDatum_symbol (j i : Fin 3) (Z : RealVectorSobolev (3 / 2)) :
    ((((derivativeHalfDatum j Z) i : RealSobolevHilbert (1 / 2)) : FourierData) :
        Space → ℂ) =ᵐ[volume]
      fun ξ => NSFormalization.Section4.R43.rieszCoordinateSymbol j ξ *
        (Z i : FourierData) ξ := by
  exact derivativeFourierDatum_ae j (Z i : FourierData)

def angularCoordinateLinearSymbol (j : Fin 3) (ξ : Space) : ℂ :=
  Complex.I * ((ξ j : ℝ) : ℂ)

theorem angularCoordinateLinearSymbol_temperate (j : Fin 3) :
    (angularCoordinateLinearSymbol j).HasTemperateGrowth := by
  change (fun ξ : Space => Complex.I *
    (Complex.ofRealCLM.comp (EuclideanSpace.proj j)) ξ).HasTemperateGrowth
  fun_prop

def angularCoordinateTest (j : Fin 3) :
    SchwartzMap Space ℂ →L[ℂ] SchwartzMap Space ℂ :=
  SchwartzMap.smulLeftCLM ℂ (angularCoordinateLinearSymbol j)

theorem angularCoordinateTest_apply (j : Fin 3) (φ : SchwartzMap Space ℂ) (ξ : Space) :
    angularCoordinateTest j φ ξ = Complex.I * ((ξ j : ℝ) : ℂ) * φ ξ := by
  simp [angularCoordinateTest, angularCoordinateLinearSymbol,
    SchwartzMap.smulLeftCLM_apply_apply (angularCoordinateLinearSymbol_temperate j)]

theorem angularFourierDistribution_lineDeriv (j : Fin 3)
    (U : TemperedDistribution Space ℂ) (φ : SchwartzMap Space ℂ) :
    angularFourierDistribution (∂_{coordinateVector j} U) φ =
      angularFourierDistribution U (angularCoordinateTest j φ) := by
  change angularDistributionDilation (𝓕 (∂_{coordinateVector j} U)) φ =
    angularDistributionDilation (𝓕 U) (angularCoordinateTest j φ)
  rw [angularDistributionDilation_apply, angularDistributionDilation_apply,
    TemperedDistribution.fourier_lineDerivOp_eq]
  congr 1
  rw [smul_apply, TemperedDistribution.smulLeftCLM_apply_apply]
  change (2 * (Real.pi : ℂ) * Complex.I) •
      (𝓕 U) ((SchwartzMap.smulLeftCLM ℂ fun x =>
        ((inner ℝ x (coordinateVector j) : ℝ) : ℂ))
          ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ angularFrequencyScale) φ)) = _
  rw [← map_smul]
  congr 1
  ext ξ
  change (2 * (Real.pi : ℂ) * Complex.I) *
      ((SchwartzMap.smulLeftCLM ℂ fun x =>
        ((inner ℝ x (coordinateVector j) : ℝ) : ℂ))
          ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ angularFrequencyScale) φ)) ξ = _
  rw [SchwartzMap.smulLeftCLM_apply_apply]
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  simp only [Function.comp_apply]
  rw [angularCoordinateTest_apply]
  rw [coordinateVector, EuclideanSpace.inner_single_right]
  simp only [one_mul, starRingEnd_apply, star_trivial, smul_eq_mul]
  rw [show angularFrequencyScale ξ = NSFormalization.Source.frequencyUnit • ξ from rfl]
  rw [show ((NSFormalization.Source.frequencyUnit • ξ) j : ℝ) =
      NSFormalization.Source.frequencyUnit * ξ j from rfl,
    Complex.ofReal_mul]
  simp only [NSFormalization.Source.frequencyUnit]
  push_cast
  ring
  all_goals fun_prop

theorem isSliceDistribution_dirDeriv {v : SpatialField}
    (hv : NSFormalization.Section4.A02.MemHInfty v) (j : Fin 3)
    {U : VectorDistribution} (hU : IsSliceDistribution v U) :
    IsSliceDistribution (dirDeriv j v) (fun i => ∂_{coordinateVector j} (U i)) := by
  let hfield : SmoothL2Field Space :=
    ⟨v, hv.1, NSFormalization.Section4.D01.memHInfty_jets hv.1 hv.2⟩
  intro i ψ
  rw [TemperedDistribution.lineDerivOp_apply_apply, hU i]
  simpa only [hfield, dirDeriv, SmoothL2Field.directionalField_field] using
    (smoothField_weakDeriv_pairing hfield j i ψ).symm

theorem isHomogeneousDatum_derivativeHalf {U : VectorDistribution}
    {Z : RealVectorSobolev (3 / 2)}
    (hZ : IsHomogeneousVectorDatum (3 / 2) U Z) (j i : Fin 3) :
    IsHomogeneousDatum (1 / 2)
      (((derivativeHalfDatum j Z) i : RealSobolevHilbert (1 / 2)) : FourierData)
      (∂_{coordinateVector j} (U i)) := by
  intro φ
  let ψ : SchwartzMap Space ℂ := angularCoordinateTest j φ
  have hsource := hZ i ψ
  have hae : (fun ξ : Space =>
        ψ ξ * (((‖ξ‖ ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * (Z i : FourierData) ξ)) =ᵐ[volume]
      fun ξ : Space => φ ξ *
        (((‖ξ‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ((((derivativeHalfDatum j Z) i : RealSobolevHilbert (1 / 2)) : FourierData) ξ)) := by
    filter_upwards [volume.ae_ne (0 : Space), derivativeHalfDatum_symbol j i Z]
      with ξ hξ hdatum
    have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    rw [angularCoordinateTest_apply, hdatum]
    simp only [NSFormalization.Section4.R43.rieszCoordinateSymbol, hξ, ite_false]
    have hpow : ‖ξ‖ ^ (-(1 / 2 : ℝ)) * (ξ j / ‖ξ‖) =
        ξ j * ‖ξ‖ ^ (-(3 / 2 : ℝ)) := by
      calc
        ‖ξ‖ ^ (-(1 / 2 : ℝ)) * (ξ j / ‖ξ‖) =
            ξ j * (‖ξ‖ ^ (-(1 / 2 : ℝ)) * ‖ξ‖ ^ (-1 : ℝ)) := by
              rw [Real.rpow_neg_one, div_eq_mul_inv]
              ring
        _ = ξ j * ‖ξ‖ ^ (-(1 / 2 : ℝ) + (-1 : ℝ)) := by
              rw [← Real.rpow_add hn]
        _ = ξ j * ‖ξ‖ ^ (-(3 / 2 : ℝ)) := by norm_num
    have hpowc : ((‖ξ‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          (((ξ j / ‖ξ‖ : ℝ) : ℂ)) =
        ((ξ j : ℝ) : ℂ) * ((‖ξ‖ ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, hpow, Complex.ofReal_mul]
    calc
      _ = φ ξ * Complex.I *
          (((ξ j : ℝ) : ℂ) * ((‖ξ‖ ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)) *
            (Z i : FourierData) ξ := by ring
      _ = φ ξ * Complex.I *
          ((((‖ξ‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            (((ξ j / ‖ξ‖ : ℝ) : ℂ)))) * (Z i : FourierData) ξ := by
              rw [hpowc]
      _ = _ := by ring
  refine ⟨hsource.1.congr hae, ?_⟩
  rw [angularFourierDistribution_lineDeriv, hsource.2, integral_congr_ae hae]

/-- U8: the Riesz-symbol datum is the actual order-half homogeneous datum of
the physical coordinate derivative. -/
theorem derivativeHalfDatum_isDatum {v : SpatialField}
    (hv : NSFormalization.Section4.A02.MemHInfty v)
    {Z : RealVectorSobolev (3 / 2)}
    (hZ : IsHomogeneousSliceDatum (3 / 2) v Z) (j : Fin 3) :
    IsHomogeneousSliceDatum (1 / 2) (dirDeriv j v) (derivativeHalfDatum j Z) := by
  obtain ⟨U, hU, hZU⟩ := hZ
  exact ⟨fun i => ∂_{coordinateVector j} (U i), isSliceDistribution_dirDeriv hv j hU,
    fun i => isHomogeneousDatum_derivativeHalf hZU j i⟩

/-- Package U4 and U8 into the exact shifted-data interface consumed by R43. -/
def shiftedCriticalData_of_memHInfty (v : SpatialField)
    (hv : NSFormalization.Section4.A02.MemHInfty v)
    (Z : RealVectorSobolev (3 / 2))
    (hZ : IsHomogeneousSliceDatum (3 / 2) v Z) :
    NSFormalization.Section4.R43.ShiftedCriticalData v Z where
  lambda := rieszLambda v hv
  lambda_memHInfty := rieszLambda_memHInfty v hv
  lambdaHalf_isDatum := rieszLambda_halfDatum v hv Z hZ
  derivativeHalf := fun j => derivativeHalfDatum j Z
  derivativeHalf_isDatum := fun j => derivativeHalfDatum_isDatum hv hZ j
  derivativeHalf_symbol := fun j i => derivativeHalfDatum_symbol j i Z

end NSFormalization.Section4.A05
