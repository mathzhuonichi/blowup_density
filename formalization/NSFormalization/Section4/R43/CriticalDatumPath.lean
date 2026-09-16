import NSFormalization.Section4.R43.Parseval
import NSFormalization.Section4.D01.PressureJets
import NSFormalization.Section4.D01.OrderZeroCurl
import NSFormalization.Section4.D01.Longitudinal
import NSFormalization.Source.BesselFractionalData

/-!
# Critical homogeneous datum paths of a classical solution

This module constructs the six half-order carriers consumed by
`CriticalPairing.CriticalDatumPath`.  The spatial construction is the bounded
Fourier multiplier

`A_s \mapsto |xi|^s (1 + |xi|^2)^(-s/2) A_s`,

from an inhomogeneous order-`s` datum.  It supplies a homogeneous datum of the
same physical field for every `s >= 0`.  The remaining time-regularity input is
isolated below in `CriticalDatumInputs`.
-/

noncomputable section

open Set MeasureTheory FourierTransform NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source
open NSFormalization.Source.RealSobolev
open scoped ContDiff ENNReal ComplexConjugate

namespace NSFormalization.Section4.R43

open NSFormalization.Section4.A02
  (SpatialField SpaceTimeField ClassicalSolutionR MemForceR)
open NSFormalization.Section4.D01
open NSFormalization.Section4.D01.Homogeneous
  (IsHomogeneousDatum IsHomogeneousSliceDatum)
open NSFormalization.Section4.D01.Leray

namespace CriticalHomogeneous

/-! ## 1. From an inhomogeneous datum to a homogeneous datum -/

/-- The bounded Bessel-to-homogeneous multiplier preserves conjugate symmetry. -/
theorem besselFractionalDatum_mem_realSubspace (s : ℝ) (hs : 0 ≤ s)
    (A : RealSobolevHilbert s) :
    BesselFractionalData.datum s hs (A : FourierData) ∈ realSubspace s := by
  rw [mem_realSubspace_iff]
  apply Lp.ext
  have hA : realSymmetry (A : FourierData) = (A : FourierData) :=
    (mem_realSubspace_iff s (A : FourierData)).mp A.2
  have hAae := realSymmetry_ae (A : FourierData)
  rw [hA] at hAae
  have hdatum_neg :=
    (Measure.measurePreserving_neg (volume : Measure Space)).quasiMeasurePreserving.ae
      (BesselFractionalData.datum_coeFn s hs (A : FourierData))
  filter_upwards [realSymmetry_ae
      (BesselFractionalData.datum s hs (A : FourierData)),
    BesselFractionalData.datum_coeFn s hs (A : FourierData),
    hdatum_neg, hAae] with ξ hsym hdatum hdatum_neg hAξ
  rw [hsym, hdatum_neg, hdatum]
  simp only [BesselFractionalData.symbol, norm_neg, map_mul,
    Complex.conj_ofReal]
  rw [← hAξ]
  simp [sobolevBesselWeight]

/-- The real scalar homogeneous datum obtained from an inhomogeneous datum of
the same nonnegative order. -/
def ofSobolevScalar (s : ℝ) (hs : 0 ≤ s) (A : RealSobolevHilbert s) :
    RealSobolevHilbert s :=
  ⟨BesselFractionalData.datum s hs (A : FourierData),
    besselFractionalDatum_mem_realSubspace s hs A⟩

/-- Pointwise Fourier formula for `ofSobolevScalar`. -/
theorem ofSobolevScalar_ae (s : ℝ) (hs : 0 ≤ s) (A : RealSobolevHilbert s) :
    ((ofSobolevScalar s hs A : RealSobolevHilbert s) : FourierData) =ᵐ[volume]
      fun ξ => BesselFractionalData.symbol s ξ * (A : FourierData) ξ :=
  BesselFractionalData.datum_coeFn s hs (A : FourierData)

/-- Removing the homogeneous weight from `ofSobolevScalar` gives the
order-zero lowering of the original Sobolev datum. -/
theorem ofSobolevScalar_weight_ae (s : ℝ) (hs : 0 ≤ s)
    (A : RealSobolevHilbert s) :
    (fun ξ : Space => ((‖ξ‖ ^ (-s) : ℝ) : ℂ) *
        (((ofSobolevScalar s hs A : RealSobolevHilbert s) : FourierData) ξ))
      =ᵐ[volume]
        fun ξ => (sobolevOrderLowering s 0 hs (A : FourierData) : FourierData) ξ := by
  filter_upwards [ofSobolevScalar_ae s hs A,
    sobolevOrderLowering_coeFn s 0 hs (A : FourierData),
    volume.ae_ne (0 : Space)] with ξ hG hlow hξ
  rw [hG, hlow]
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  simp only [BesselFractionalData.symbol, sobolevBesselWeight, zero_sub]
  have hcancel : ‖ξ‖ ^ (-s) * ‖ξ‖ ^ s = 1 := by
    rw [← Real.rpow_add hn]
    simp
  have hcancelc : ((‖ξ‖ ^ (-s) : ℝ) : ℂ) * ((‖ξ‖ ^ s : ℝ) : ℂ) = 1 := by
    exact_mod_cast hcancel
  calc
    _ = (((‖ξ‖ ^ (-s) : ℝ) : ℂ) * ((‖ξ‖ ^ s : ℝ) : ℂ)) *
        (((1 + ‖ξ‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ) * (A : FourierData) ξ := by ring
    _ = _ := by rw [hcancelc]; simp

/-- The scalar multiplier realizes the same physical tempered distribution as
the inhomogeneous datum. -/
theorem ofSobolevScalar_isHomogeneousDatum (s : ℝ) (hs : 0 ≤ s)
    (A : RealSobolevHilbert s) :
    IsHomogeneousDatum s (ofSobolevScalar s hs A : FourierData)
      (angularRealization s (A : FourierData)) := by
  have hangular : angularFourierDistribution
        (angularRealization s (A : FourierData)) =
      (sobolevOrderLowering s 0 hs (A : FourierData) : TemperedDistribution Space ℂ) := by
    have h := congrArg (sobolevWeightMultiplier (-s))
      (weightedAngularFourier_realization s (A : FourierData))
    simpa only [sobolevWeightMultiplier_add, add_neg_cancel,
      sobolevWeightMultiplier_zero,
      zero_sub,
      sobolevOrderLowering_toDistribution s 0 hs (A : FourierData)] using h
  intro φ
  have hprod :
      (fun ξ : Space => φ ξ * (((‖ξ‖ ^ (-s) : ℝ) : ℂ) *
        ((ofSobolevScalar s hs A : RealSobolevHilbert s) : FourierData) ξ))
        =ᵐ[volume]
      fun ξ => φ ξ * (sobolevOrderLowering s 0 hs (A : FourierData) : FourierData) ξ := by
    filter_upwards [ofSobolevScalar_weight_ae s hs A] with ξ hξ
    rw [hξ]
  have hint : Integrable (fun ξ : Space =>
      φ ξ * (sobolevOrderLowering s 0 hs (A : FourierData) : FourierData) ξ) :=
    (φ.memLp 2 volume).integrable_mul (Lp.memLp _)
  refine ⟨hint.congr hprod.symm, ?_⟩
  rw [hangular, Lp.toTemperedDistribution_apply]
  simpa only [smul_eq_mul] using integral_congr_ae hprod.symm

/-- Componentwise Bessel-to-homogeneous conversion. -/
def ofSobolevVector (s : ℝ) (hs : 0 ≤ s) (A : RealVectorSobolev s) :
    RealVectorSobolev s :=
  WithLp.toLp 2 (fun i => ofSobolevScalar s hs (A i))

@[simp] theorem ofSobolevVector_apply (s : ℝ) (hs : 0 ≤ s)
    (A : RealVectorSobolev s) (i : Fin 3) :
    ofSobolevVector s hs A i = ofSobolevScalar s hs (A i) := rfl

/-- Every inhomogeneous datum at a nonnegative order canonically yields a
homogeneous datum of the same physical field. -/
theorem ofSobolevVector_isHomogeneousSliceDatum {s : ℝ} (hs : 0 ≤ s)
    {z : Homogeneous.SpatialField} {A : RealVectorSobolev s} (hA : IsSobolevDatum s z A) :
    IsHomogeneousSliceDatum s z (ofSobolevVector s hs A) := by
  refine ⟨fun i => angularRealization s (A i : FourierData), hA, ?_⟩
  intro i
  exact ofSobolevScalar_isHomogeneousDatum s hs (A i)

/-- Canonical homogeneous datum of a smooth field with square-integrable jets. -/
def ofSmoothL2 (s : ℝ) (hs : 0 ≤ s)
    (Z : EulerLpTranslation.SmoothL2Field Space) : RealVectorSobolev s :=
  ofSobolevVector s hs
    (smoothAngularDatum ⌈s⌉₊ s (Nat.le_ceil s) Z)

/-- The canonical datum `ofSmoothL2` realizes the physical field. -/
theorem ofSmoothL2_isHomogeneousSliceDatum (s : ℝ) (hs : 0 ≤ s)
    (Z : EulerLpTranslation.SmoothL2Field Space) :
    IsHomogeneousSliceDatum s Z.field (ofSmoothL2 s hs Z) :=
  ofSobolevVector_isHomogeneousSliceDatum hs
    (smoothAngularDatum_isSobolevDatum ⌈s⌉₊ s (Nat.le_ceil s) Z)

end CriticalHomogeneous

/-! ## 2. The six datum paths -/

/-- A total choice of homogeneous datum.  On fields outside the solution
interval it defaults to zero; on every slice used below the existence branch is
selected and uniqueness makes the choice canonical. -/
def chosenHomogeneousDatum (s : ℝ) (z : Homogeneous.SpatialField) :
    RealVectorSobolev s := by
  classical
  exact if h : ∃ A : RealVectorSobolev s, IsHomogeneousSliceDatum s z A then
      Classical.choose h
    else 0

theorem chosenHomogeneousDatum_isDatum {s : ℝ} {z : Homogeneous.SpatialField}
    (h : ∃ A : RealVectorSobolev s, IsHomogeneousSliceDatum s z A) :
    IsHomogeneousSliceDatum s z (chosenHomogeneousDatum s z) := by
  classical
  rw [chosenHomogeneousDatum, dite_eq_left h]
  exact Classical.choose_spec h

/-- Smooth square-integrable spatial jets have homogeneous data at every
nonnegative real order. -/
theorem exists_isHomogeneousSliceDatum_of_smoothL2 {z : Homogeneous.SpatialField}
    (hz : SmoothSquareIntegrableJets z) (s : ℝ) (hs : 0 ≤ s) :
    ∃ A : RealVectorSobolev s, IsHomogeneousSliceDatum s z A := by
  let Z : EulerLpTranslation.SmoothL2Field Space := ⟨z, hz.1, hz.2⟩
  exact ⟨CriticalHomogeneous.ofSmoothL2 s hs Z,
    CriticalHomogeneous.ofSmoothL2_isHomogeneousSliceDatum s hs Z⟩

/-- The order-half velocity datum path. -/
def criticalVelocityHalf
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionR ν a f T) (t : ℝ) : RealVectorSobolev (1 / 2) :=
  chosenHomogeneousDatum (1 / 2) (fun x => w.velocity (t, x))

/-- The order-three-halves velocity datum path. -/
def criticalVelocityThreeHalf
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionR ν a f T) (t : ℝ) : RealVectorSobolev (3 / 2) :=
  chosenHomogeneousDatum (3 / 2) (fun x => w.velocity (t, x))

/-- The order-half datum path of the spatial Laplacian. -/
def criticalLaplacianHalf
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionR ν a f T) (t : ℝ) : RealVectorSobolev (1 / 2) :=
  chosenHomogeneousDatum (1 / 2) (fun x => spatialLaplacian w.velocity t x)

/-- The order-half datum path of advection. -/
def criticalAdvectionHalf
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionR ν a f T) (t : ℝ) : RealVectorSobolev (1 / 2) :=
  chosenHomogeneousDatum (1 / 2) (fun x => advection w.velocity t x)

/-- The order-half datum path of the pressure gradient. -/
def criticalPressureHalf
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionR ν a f T) (t : ℝ) : RealVectorSobolev (1 / 2) :=
  chosenHomogeneousDatum (1 / 2) (fun x => pressureGradient w.pressure t x)

/-- The order-half datum path of the force. -/
def criticalForceHalf
    {f : SpaceTimeField} (t : ℝ) : RealVectorSobolev (1 / 2) :=
  chosenHomogeneousDatum (1 / 2) (fun x => f (t, x))

theorem criticalVelocityHalf_isDatum
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionR ν a f T) :
    ∀ t ∈ Ico (0 : ℝ) T,
      IsHomogeneousSliceDatum (1 / 2) (fun x => w.velocity (t, x))
        (criticalVelocityHalf w t) := by
  intro t ht
  apply chosenHomogeneousDatum_isDatum
  exact exists_isHomogeneousSliceDatum_of_smoothL2
    (NSFormalization.Section4.C01.velocity_slice_smoothL2 w ht) (1 / 2) (by norm_num)

theorem criticalVelocityThreeHalf_isDatum
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionR ν a f T) :
    ∀ t ∈ Ico (0 : ℝ) T,
      IsHomogeneousSliceDatum (3 / 2) (fun x => w.velocity (t, x))
        (criticalVelocityThreeHalf w t) := by
  intro t ht
  apply chosenHomogeneousDatum_isDatum
  exact exists_isHomogeneousSliceDatum_of_smoothL2
    (NSFormalization.Section4.C01.velocity_slice_smoothL2 w ht) (3 / 2) (by norm_num)

theorem criticalLaplacianHalf_isDatum
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionR ν a f T) :
    ∀ t ∈ Ioo (0 : ℝ) T,
      IsHomogeneousSliceDatum (1 / 2)
        (fun x => spatialLaplacian w.velocity t x) (criticalLaplacianHalf w t) := by
  intro t ht
  apply chosenHomogeneousDatum_isDatum
  exact exists_isHomogeneousSliceDatum_of_smoothL2
    (laplacian_slice_smoothL2 w ht) (1 / 2) (by norm_num)

theorem criticalAdvectionHalf_isDatum
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionR ν a f T) :
    ∀ t ∈ Ioo (0 : ℝ) T,
      IsHomogeneousSliceDatum (1 / 2)
        (fun x => advection w.velocity t x) (criticalAdvectionHalf w t) := by
  intro t ht
  apply chosenHomogeneousDatum_isDatum
  exact exists_isHomogeneousSliceDatum_of_smoothL2
    (advection_slice_smoothL2 w ht) (1 / 2) (by norm_num)

theorem criticalPressureHalf_isDatum
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionR ν a f T)
    (hf : NSFormalization.Section4.A02.MemForceR f) :
    ∀ t ∈ Ioo (0 : ℝ) T,
      IsHomogeneousSliceDatum (1 / 2)
        (fun x => pressureGradient w.pressure t x) (criticalPressureHalf w t) := by
  intro t ht
  apply chosenHomogeneousDatum_isDatum
  exact exists_isHomogeneousSliceDatum_of_smoothL2
    (pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR w hf ht)
    (1 / 2) (by norm_num)

theorem criticalForceHalf_isDatum
    {f : SpaceTimeField} (hf : NSFormalization.Section4.A02.MemForceR f) :
    ∀ t, 0 ≤ t →
      IsHomogeneousSliceDatum (1 / 2) (fun x => f (t, x))
        (criticalForceHalf (f := f) t) := by
  intro t ht
  apply chosenHomogeneousDatum_isDatum
  exact exists_isHomogeneousSliceDatum_of_smoothL2
    (forceSlice_smoothL2_of_memForceR hf ht) (1 / 2) (by norm_num)

/-! ## 3. Compatibility of the spatial carriers -/

/-- At order zero the canonical datum is exactly the normalized angular
Fourier transform of the physical `L²` representative. -/
theorem orderZeroDatum_angular_ae {z : SpatialField} (hz : MemLp z 2 volume)
    (i : Fin 3) :
    (((orderZeroDatum hz) i : FourierData) : Space → ℂ) =ᵐ[volume]
      (angularFrequencyDilation
        (FourierTransform.fourier (componentLp hz i)) : Space → ℂ) := by
  have hw : angularWeightEquiv 0
      (FourierTransform.fourier (componentLp hz i)) =
      FourierTransform.fourier (componentLp hz i) := by
    apply Lp.ext
    filter_upwards [angularWeightEquiv_coeFn 0
      (FourierTransform.fourier (componentLp hz i))] with ξ hξ
    rw [hξ]
    simp [angularWeightSymbol, sobolevBesselWeight]
  rw [orderZeroDatum_coe]
  change (angularFrequencyDilation
      (angularWeightEquiv 0 (FourierTransform.fourier (componentLp hz i))) :
        Space → ℂ) =ᵐ[volume] _
  rw [hw]

/-- The two homogeneous velocity carriers are the same angular Fourier
transform with weights differing by one power of frequency. -/
theorem criticalVelocity_order_shift
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionR ν a f T) :
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ i : Fin 3,
      ((((criticalVelocityThreeHalf w t) i : RealSobolevHilbert (3 / 2)) :
          FourierData) : Space → ℂ) =ᵐ[volume]
        fun ξ => ((‖ξ‖ : ℝ) : ℂ) *
          ((criticalVelocityHalf w t) i : FourierData) ξ := by
  intro t ht i
  have hu := (NSFormalization.Section4.C01.velocity_slice_smoothL2 w
    (Ioo_subset_Ico_self ht)).memLp
  have hhalf := homogeneous_slice_angular_ae hu
    (criticalVelocityHalf_isDatum w t (Ioo_subset_Ico_self ht)) i
  have hthree := homogeneous_slice_angular_ae hu
    (criticalVelocityThreeHalf_isDatum w t (Ioo_subset_Ico_self ht)) i
  filter_upwards [hhalf, hthree, volume.ae_ne (0 : Space)] with ξ hhalf hthree hξ
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hp : ‖ξ‖ ^ (-(3 / 2 : ℝ)) * ‖ξ‖ = ‖ξ‖ ^ (-(1 / 2 : ℝ)) := by
    nth_rewrite 2 [← Real.rpow_one ‖ξ‖]
    rw [← Real.rpow_add hn]
    norm_num
  have hpc : ((‖ξ‖ ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * ((‖ξ‖ : ℝ) : ℂ) =
      ((‖ξ‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    exact_mod_cast hp
  have hc : ((‖ξ‖ ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos hn (-(3 / 2 : ℝ))).ne'
  apply (mul_left_cancel₀ hc)
  calc
    ((‖ξ‖ ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
          ((criticalVelocityThreeHalf w t) i : FourierData) ξ =
        (angularFrequencyDilation
          (FourierTransform.fourier (componentLp hu i)) : Space → ℂ) ξ := hthree.symm
    _ = ((‖ξ‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ((criticalVelocityHalf w t) i : FourierData) ξ := hhalf
    _ = ((‖ξ‖ ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
          (((‖ξ‖ : ℝ) : ℂ) *
            ((criticalVelocityHalf w t) i : FourierData) ξ) := by rw [← hpc]; ring

/-- The component `L²` class of the physical Laplacian is the sum of the
component classes of its three second directional derivatives. -/
theorem componentLp_laplacianField
    (Z : EulerLpTranslation.SmoothL2Field Space) (i : Fin 3) :
    componentLp
        (NSFormalization.Source.OrdinaryViscousStability.laplacianField Z).memLp i =
      ∑ j : Fin 3, componentLp
        ((Z.directionalField (coordinateVector j)).directionalField
          (coordinateVector j)).memLp i := by
  rw [NSFormalization.Section4.A05.componentLp_smoothField]
  simp only [NSFormalization.Source.OrdinaryViscousStability.laplacianField,
    EulerOrdinarySobolev.toLp_sumField, map_sum,
    NSFormalization.Source.FiniteHilbertBochner.coordinates]
  apply Finset.sum_congr rfl
  intro j _
  exact (NSFormalization.Section4.A05.componentLp_smoothField
    ((Z.directionalField (coordinateVector j)).directionalField
      (coordinateVector j)) i).symm

/-- In cycles frequency, the physical Laplacian has multiplier
`-frequencyUnit² * |ξ|²`. -/
theorem fourier_laplacianField_component_ae
    (Z : EulerLpTranslation.SmoothL2Field Space) (i : Fin 3) :
    ((FourierTransform.fourier
        (componentLp
          (NSFormalization.Source.OrdinaryViscousStability.laplacianField Z).memLp i) :
        FourierData) : Space → ℂ) =ᵐ[volume]
      fun ξ => -(((NSFormalization.Source.frequencyUnit ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) *
        (FourierTransform.fourier (componentLp Z.memLp i) : FourierData) ξ) := by
  have hlp := congrArg (fourierCLM ℂ FourierData) (componentLp_laplacianField Z i)
  have hlp' : FourierTransform.fourier
        (componentLp
          (NSFormalization.Source.OrdinaryViscousStability.laplacianField Z).memLp i) =
      ∑ j : Fin 3, FourierTransform.fourier
        (componentLp
          ((Z.directionalField (coordinateVector j)).directionalField
            (coordinateVector j)).memLp i) := by
    simpa only [map_sum, fourierCLM_apply] using hlp
  have hfirst : ∀ᵐ ξ : Space ∂volume, ∀ j : Fin 3,
      (FourierTransform.fourier
          (componentLp (Z.directionalField (coordinateVector j)).memLp i) :
          FourierData) ξ =
        (2 * (Real.pi : ℂ) * Complex.I) * ((ξ j : ℝ) : ℂ) *
          (FourierTransform.fourier (componentLp Z.memLp i) : FourierData) ξ := by
    rw [ae_all_iff]
    intro j
    have h := NSFormalization.Section4.A05.fourier_directionalField_component_ae Z j i
    rw [NSFormalization.Section4.A05.coordinates_fourier,
      NSFormalization.Section4.A05.coordinates_fourier,
      ← NSFormalization.Section4.A05.componentLp_smoothField
        (Z.directionalField (coordinateVector j)) i,
      ← NSFormalization.Section4.A05.componentLp_smoothField Z i] at h
    exact h
  have hsecond : ∀ᵐ ξ : Space ∂volume, ∀ j : Fin 3,
      (FourierTransform.fourier
          (componentLp
            ((Z.directionalField (coordinateVector j)).directionalField
              (coordinateVector j)).memLp i) : FourierData) ξ =
        ((2 * (Real.pi : ℂ) * Complex.I) * ((ξ j : ℝ) : ℂ)) *
          ((2 * (Real.pi : ℂ) * Complex.I) * ((ξ j : ℝ) : ℂ)) *
          (FourierTransform.fourier (componentLp Z.memLp i) : FourierData) ξ := by
    rw [ae_all_iff]
    intro j
    have h := NSFormalization.Section4.A05.fourier_directionalField_component_ae
      (Z.directionalField (coordinateVector j)) j i
    rw [NSFormalization.Section4.A05.coordinates_fourier,
      NSFormalization.Section4.A05.coordinates_fourier,
      ← NSFormalization.Section4.A05.componentLp_smoothField
        ((Z.directionalField (coordinateVector j)).directionalField
          (coordinateVector j)) i,
      ← NSFormalization.Section4.A05.componentLp_smoothField
        (Z.directionalField (coordinateVector j)) i] at h
    filter_upwards [h, hfirst] with ξ h hfirst
    rw [h, hfirst j]
    ring
  rw [hlp']
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun j : Fin 3 =>
      FourierTransform.fourier
        (componentLp
          ((Z.directionalField (coordinateVector j)).directionalField
            (coordinateVector j)).memLp i)), hsecond] with ξ hsum hsecond
  rw [hsum]
  simp only [Finset.sum_apply]
  rw [Finset.sum_congr rfl (fun j _ => hsecond j)]
  have hsq : ‖ξ‖ ^ 2 = ∑ j : Fin 3, (ξ j) ^ 2 := by
    simpa [Real.norm_eq_abs, sq_abs] using
      (PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) ξ)
  have hcoeff :
      (∑ j : Fin 3,
        ((2 * (Real.pi : ℂ) * Complex.I) * ((ξ j : ℝ) : ℂ)) *
          ((2 * (Real.pi : ℂ) * Complex.I) * ((ξ j : ℝ) : ℂ))) =
        -((NSFormalization.Source.frequencyUnit ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) := by
    calc
      _ = -((((2 * Real.pi) ^ 2 : ℝ) : ℂ) *
          (((∑ j : Fin 3, (ξ j) ^ 2 : ℝ) : ℂ))) := by
            rw [Fin.sum_univ_three]
            push_cast
            ring_nf
            rw [Complex.I_sq, Fin.sum_univ_three]
            ring
      _ = -(((NSFormalization.Source.frequencyUnit ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ)) := by
            rw [← hsq]
            simp only [NSFormalization.Source.frequencyUnit]
            push_cast
            ring
  calc
    _ = (∑ j : Fin 3,
        ((2 * (Real.pi : ℂ) * Complex.I) * ((ξ j : ℝ) : ℂ)) *
          ((2 * (Real.pi : ℂ) * Complex.I) * ((ξ j : ℝ) : ℂ))) *
        (FourierTransform.fourier (componentLp Z.memLp i) : FourierData) ξ := by
          rw [Finset.sum_mul]
    _ = _ := by rw [hcoeff]; ring

/-- Normalized angular dilation converts the cycles Laplacian symbol to the
manuscript symbol `-|ξ|²`. -/
theorem angular_laplacianField_component_ae
    (Z : EulerLpTranslation.SmoothL2Field Space) (i : Fin 3) :
    (angularFrequencyDilation
        (FourierTransform.fourier
          (componentLp
            (NSFormalization.Source.OrdinaryViscousStability.laplacianField Z).memLp i)) :
      Space → ℂ) =ᵐ[volume]
      fun ξ => -(((‖ξ‖ ^ 2 : ℝ) : ℂ) *
        (angularFrequencyDilation
          (FourierTransform.fourier (componentLp Z.memLp i)) : FourierData) ξ) := by
  have hqmp : Measure.QuasiMeasurePreserving
      (fun ξ : Space => NSFormalization.Source.frequencyUnit⁻¹ • ξ) volume volume := by
    refine ⟨(continuous_const_smul _).measurable, ?_⟩
    rw [Measure.map_addHaar_smul volume
      (inv_ne_zero NSFormalization.Source.frequencyUnit_pos.ne')]
    exact Measure.smul_absolutelyContinuous
  have hraw := hqmp.ae (fourier_laplacianField_component_ae Z i)
  have hL := NSFormalization.Paper3.angularFrequencyDilation_coeFn
    (FourierTransform.fourier
      (componentLp
        (NSFormalization.Source.OrdinaryViscousStability.laplacianField Z).memLp i))
  have hZ := NSFormalization.Paper3.angularFrequencyDilation_coeFn
    (FourierTransform.fourier (componentLp Z.memLp i))
  filter_upwards [hL, hZ, hraw] with ξ hL hZ hraw
  rw [hL, hraw, hZ]
  have hc : 0 < NSFormalization.Source.frequencyUnit :=
    NSFormalization.Source.frequencyUnit_pos
  have hnorm : NSFormalization.Source.frequencyUnit ^ 2 *
      ‖NSFormalization.Source.frequencyUnit⁻¹ • ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
    field_simp [hc.ne']
  rw [hnorm]
  simp only [Complex.real_smul]
  ring

/-- The chosen half-order datum of the physical Laplacian has multiplier
`-|ξ|²` relative to the chosen half-order velocity datum. -/
theorem criticalLaplacian_symbol
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionR ν a f T) :
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ i : Fin 3,
      ((((criticalLaplacianHalf w t) i : RealSobolevHilbert (1 / 2)) :
          FourierData) : Space → ℂ) =ᵐ[volume]
        fun ξ => -(((‖ξ‖ ^ 2 : ℝ) : ℂ) *
          ((criticalVelocityHalf w t) i : FourierData) ξ) := by
  intro t ht i
  let Z := NSFormalization.Section4.C01.velocitySliceField w
    (Ioo_subset_Ico_self ht)
  let L := NSFormalization.Source.OrdinaryViscousStability.laplacianField Z
  have hLfield : L.field = fun x => spatialLaplacian w.velocity t x := by
    funext x
    exact NSFormalization.Section4.C01.laplacianField_velocitySlice_field w
      (Ioo_subset_Ico_self ht) x
  have hlapDatum : IsHomogeneousSliceDatum (1 / 2) L.field
      (criticalLaplacianHalf w t) := by
    rw [hLfield]
    exact criticalLaplacianHalf_isDatum w t ht
  have hvelDatum : IsHomogeneousSliceDatum (1 / 2) Z.field
      (criticalVelocityHalf w t) := by
    exact criticalVelocityHalf_isDatum w t (Ioo_subset_Ico_self ht)
  have hlap := homogeneous_slice_angular_ae L.memLp hlapDatum i
  have hvel := homogeneous_slice_angular_ae Z.memLp hvelDatum i
  have hsymbol := angular_laplacianField_component_ae Z i
  filter_upwards [hlap, hvel, hsymbol, volume.ae_ne (0 : Space)]
    with ξ hlap hvel hsymbol hξ
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hc : ((‖ξ‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos hn (-(1 / 2 : ℝ))).ne'
  apply (mul_left_cancel₀ hc)
  calc
    ((‖ξ‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ((criticalLaplacianHalf w t) i : FourierData) ξ =
        (angularFrequencyDilation
          (FourierTransform.fourier (componentLp L.memLp i)) : Space → ℂ) ξ := hlap.symm
    _ = -(((‖ξ‖ ^ 2 : ℝ) : ℂ) *
          (angularFrequencyDilation
            (FourierTransform.fourier (componentLp Z.memLp i)) : FourierData) ξ) := hsymbol
    _ = -(((‖ξ‖ ^ 2 : ℝ) : ℂ) *
          (((‖ξ‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ((criticalVelocityHalf w t) i : FourierData) ξ)) := by rw [hvel]
    _ = ((‖ξ‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          -(((‖ξ‖ ^ 2 : ℝ) : ℂ) *
            ((criticalVelocityHalf w t) i : FourierData) ξ) := by ring

/-- Divergence-freeness of the classical velocity passes to its half-order
homogeneous datum. -/
theorem criticalVelocity_transverse
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionR ν a f T) :
    ∀ t ∈ Ioo (0 : ℝ) T,
      lerayComplement (1 / 2) (criticalVelocityHalf w t) = 0 := by
  intro t ht
  let Z : EulerLpTranslation.SmoothL2Field Space :=
    ⟨fun x => w.velocity (t, x),
      (NSFormalization.Section4.C01.velocity_slice_smoothL2 w
        (Ioo_subset_Ico_self ht)).1,
      (NSFormalization.Section4.C01.velocity_slice_smoothL2 w
        (Ioo_subset_Ico_self ht)).2⟩
  have hdiv : ∀ x, ∑ j : Fin 3,
      NSFormalization.Section4.A03.partialDeriv j Z.field x j = 0 := by
    intro x
    simpa [Z, NSFormalization.Section4.A03.partialDeriv,
      NSFormalization.Section4.A03.lift, spatialDivergence, spatialDerivative,
      coordinateVector] using
      w.divergence t (Ioo_subset_Ico_self ht) x
  have htrans0 := orderZeroDatum_transverse_of_divergence_free
    Z.memLp Z.smooth hdiv
  have hzero : ∀ᵐ ξ : Space ∂volume, ∀ j : Fin 3,
      ((orderZeroDatum Z.memLp j : FourierData) ξ) =
        (angularFrequencyDilation
          (FourierTransform.fourier (componentLp Z.memLp j)) : Space → ℂ) ξ := by
    rw [ae_all_iff]
    exact fun j => orderZeroDatum_angular_ae Z.memLp j
  have hhalf : ∀ᵐ ξ : Space ∂volume, ∀ j : Fin 3,
      (angularFrequencyDilation
          (FourierTransform.fourier (componentLp Z.memLp j)) : Space → ℂ) ξ =
        ((‖ξ‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ((criticalVelocityHalf w t) j : FourierData) ξ := by
    rw [ae_all_iff]
    intro j
    exact homogeneous_slice_angular_ae Z.memLp
      (criticalVelocityHalf_isDatum w t (Ioo_subset_Ico_self ht)) j
  apply lerayComplement_eq_zero_of_transverse
  filter_upwards [htrans0, hzero, hhalf, volume.ae_ne (0 : Space)]
    with ξ htrans0 hzero hhalf hξ
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hc : ((‖ξ‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos hn (-(1 / 2 : ℝ))).ne'
  have hweighted : ((‖ξ‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      (∑ j : Fin 3, ((ξ j : ℝ) : ℂ) *
        ((criticalVelocityHalf w t) j : FourierData) ξ) = 0 := by
    calc
      _ = ∑ j : Fin 3, ((ξ j : ℝ) : ℂ) *
          (((‖ξ‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ((criticalVelocityHalf w t) j : FourierData) ξ) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = ∑ j : Fin 3, ((ξ j : ℝ) : ℂ) *
          (angularFrequencyDilation
            (FourierTransform.fourier (componentLp Z.memLp j)) : Space → ℂ) ξ := by
              apply Finset.sum_congr rfl
              intro j _
              rw [hhalf j]
      _ = ∑ j : Fin 3, ((ξ j : ℝ) : ℂ) *
          ((orderZeroDatum Z.memLp j : FourierData) ξ) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [hzero j]
      _ = 0 := htrans0
  exact (mul_eq_zero.mp hweighted).resolve_left hc

/-- A pressure gradient is curl-free, hence its half-order homogeneous datum
is fixed by the Leray complement. -/
theorem criticalPressure_longitudinal
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionR ν a f T)
    (hf : NSFormalization.Section4.A02.MemForceR f) :
    ∀ t ∈ Ioo (0 : ℝ) T,
      ∃ Q : RealVectorSobolev (1 / 2),
        criticalPressureHalf w t = lerayComplement (1 / 2) Q := by
  intro t ht
  let Z : EulerLpTranslation.SmoothL2Field Space :=
    ⟨fun x => pressureGradient w.pressure t x,
      (pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR w hf ht).1,
      (pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR w hf ht).2⟩
  have hlong0 := orderZeroDatum_longitudinal_of_curl_free
    Z.memLp Z.smooth (fun i j x => partialDeriv_pressureGradient_symm w ht i j x)
  have hzero : ∀ᵐ ξ : Space ∂volume, ∀ j : Fin 3,
      ((orderZeroDatum Z.memLp j : FourierData) ξ) =
        (angularFrequencyDilation
          (FourierTransform.fourier (componentLp Z.memLp j)) : Space → ℂ) ξ := by
    rw [ae_all_iff]
    exact fun j => orderZeroDatum_angular_ae Z.memLp j
  have hhalf : ∀ᵐ ξ : Space ∂volume, ∀ j : Fin 3,
      (angularFrequencyDilation
          (FourierTransform.fourier (componentLp Z.memLp j)) : Space → ℂ) ξ =
        ((‖ξ‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ((criticalPressureHalf w t) j : FourierData) ξ := by
    rw [ae_all_iff]
    intro j
    exact homogeneous_slice_angular_ae Z.memLp
      (criticalPressureHalf_isDatum w hf t ht) j
  have hlong : ∀ᵐ ξ : Space ∂volume, ∀ i j : Fin 3,
      ((ξ i : ℝ) : ℂ) * ((criticalPressureHalf w t) j : FourierData) ξ =
        ((ξ j : ℝ) : ℂ) * ((criticalPressureHalf w t) i : FourierData) ξ := by
    filter_upwards [hlong0, hzero, hhalf, volume.ae_ne (0 : Space)]
      with ξ hlong0 hzero hhalf hξ
    intro i j
    have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    have hc : ((‖ξ‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.rpow_pos_of_pos hn (-(1 / 2 : ℝ))).ne'
    apply (mul_left_cancel₀ hc)
    calc
      _ = ((ξ i : ℝ) : ℂ) *
          (((‖ξ‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ((criticalPressureHalf w t) j : FourierData) ξ) := by ring
      _ = ((ξ i : ℝ) : ℂ) *
          (angularFrequencyDilation
            (FourierTransform.fourier (componentLp Z.memLp j)) : Space → ℂ) ξ := by
              rw [hhalf j]
      _ = ((ξ i : ℝ) : ℂ) * ((orderZeroDatum Z.memLp j : FourierData) ξ) := by
              rw [hzero j]
      _ = ((ξ j : ℝ) : ℂ) * ((orderZeroDatum Z.memLp i : FourierData) ξ) := hlong0 i j
      _ = ((ξ j : ℝ) : ℂ) *
          (angularFrequencyDilation
            (FourierTransform.fourier (componentLp Z.memLp i)) : Space → ℂ) ξ := by
              rw [hzero i]
      _ = ((ξ j : ℝ) : ℂ) *
          (((‖ξ‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ((criticalPressureHalf w t) i : FourierData) ξ) := by
              rw [hhalf i]
      _ = ((‖ξ‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          (((ξ j : ℝ) : ℂ) *
            ((criticalPressureHalf w t) i : FourierData) ξ) := by ring
  have hfixed := lerayComplement_eq_self_of_longitudinal
    (1 / 2) (criticalPressureHalf w t) hlong
  exact ⟨criticalPressureHalf w t, hfixed.symm⟩

/-! ## 4. The remaining time-path input -/

/-- The precise time-regularity facts still absent for an arbitrary
`ClassicalSolutionR` in the current tree.  Both clauses are standard
properties of the homogeneous half-order trajectory of a classical solution:
smoothness as a Hilbert-valued path and the Navier--Stokes momentum equation
after applying the half-order Fourier multiplier.  No spatial existence,
symbol, solenoidality, pressure, or estimate hypothesis is included. -/
structure CriticalDatumInputs
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionR ν a f T)
    (_hf : NSFormalization.Section4.A02.MemForceR f) : Prop where
  velocityHalf_smooth :
    ContDiffOn ℝ ∞ (criticalVelocityHalf w) (Ico (0 : ℝ) T)
  momentum : ∀ t ∈ Ioo (0 : ℝ) T,
    deriv (criticalVelocityHalf w) t =
      ν • criticalLaplacianHalf w t - criticalAdvectionHalf w t -
        criticalPressureHalf w t + criticalForceHalf (f := f) t

end NSFormalization.Section4.R43
