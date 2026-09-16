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

end NSFormalization.Section4.R43
