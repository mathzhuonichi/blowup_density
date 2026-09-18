import NSFormalization.Section3.T12.CriticalL3Density

/-!
# U4b closure probe (lane 401)

`Section3/T12/CriticalL3Density.lean` proves the **verbatim** API field
`velocityCriticalL3` of `MeanZeroSobolevCalculusAPI`
(`research/T12/probes/api_on_canonical.lean:148-151`), with the same constant
`CcriticalHalf` as lane 396's smooth form.  This probe

* closes the canonical API shape by `exact` (the `∀`-form, unmodified);
* records the truncation machinery it goes through;
* instantiates hypothesis **and** conclusion on the genuine nonzero smooth
  mean-zero periodic witness `probeMZ = meanZeroPartT (x ↦ cos(2π x₀)·e₀)`
  (lane 377/396's witness, reproduced here since research probes cannot import
  one another), whose `MemPeriodicHomogeneous (1/2)` membership is supplied by
  `memPeriodicHomogeneous_of_smooth`, so nothing is vacuous.
-/

noncomputable section

namespace NSFormalization.Section3.T12

open Set Filter MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13
open NSFormalization.Section4.A02 (SpatialField)
open scoped ContDiff ENNReal BigOperators Topology Real

/-! ## 1. The API field, verbatim -/

example :
    ∀ v : SpatialField, MemPeriodicHomogeneous (1 / 2) v →
      periodicLpENorm 3 v ≤
        ENNReal.ofReal CcriticalHalf * periodicHomogeneousENorm (1 / 2) v :=
  velocityCriticalL3

example (v : SpatialField) (hv : MemPeriodicHomogeneous (1 / 2) v) :
    periodicLpENorm 3 v
      ≤ ENNReal.ofReal CcriticalHalf * periodicHomogeneousENorm (1 / 2) v :=
  velocityCriticalL3 v hv

example : 0 < CcriticalHalf := CcriticalHalf_pos

/-! ## 2. The density machinery the proof goes through -/

/-- The truncation is a smooth periodic field. -/
example (v : SpatialField) (S : Finset PeriodicFrequency) :
    SmoothPeriodicT (truncField v S) := smoothPeriodicT_truncField v S

/-- Its Fourier datum is the restriction of the datum of `v`. -/
example (v : SpatialField) (S : Finset PeriodicFrequency) (hS : ∀ k ∈ S, -k ∈ S)
    (i : Fin 3) (m : PeriodicFrequency) :
    periodicFourierCoeff (fun y => ((truncField v S y i : ℝ) : ℂ)) m
      = if m ∈ S then periodicFourierCoeff (fun y => ((v y i : ℝ) : ℂ)) m else 0 :=
  periodicFourierCoeff_truncField v S hS i m

/-- Truncation does not increase the homogeneous norm. -/
example (s : ℝ) (v : SpatialField) (hL : MemLp (torusLift v) 2 periodicTorusMeasure)
    (hmean : IsMeanZeroT v) (S : Finset PeriodicFrequency) (hS : ∀ k ∈ S, -k ∈ S) :
    periodicHomogeneousENorm s (truncField v S) ≤ periodicHomogeneousENorm s v :=
  periodicHomogeneousENorm_truncField_le s v hL hmean S hS

/-- The truncations converge in `L²(T³)`. -/
example (v : SpatialField) (hL : MemLp (torusLift v) 2 periodicTorusMeasure) :
    Tendsto (fun N : ℕ =>
        eLpNorm (fun z => torusLift (truncField v (freqBox N)) z - torusLift v z) 2
          periodicTorusMeasure) atTop (𝓝 0) :=
  tendsto_eLpNorm_truncField_sub v hL

/-- The frequency boxes are symmetric and cofinal. -/
example (N : ℕ) : ∀ k ∈ freqBox N, -k ∈ freqBox N := freqBox_neg_closed N

example : Tendsto freqBox atTop atTop := tendsto_freqBox

/-! ## 3. A genuine nonzero smooth mean-zero periodic witness -/

/-- A single-mode cosine vector field, `x ↦ cos(2π x₀)·e₀`. -/
def densityProbeZ : SpatialField :=
  fun x => Real.cos (2 * Real.pi * x 0) • coordinateVector 0

theorem densityProbeZ_contDiff : ContDiff ℝ ∞ densityProbeZ := by
  unfold densityProbeZ
  have hproj : ContDiff ℝ ∞ (fun x : Space => x 0) := contDiff_piLp_apply 2
  exact (Real.contDiff_cos.comp (contDiff_const.mul hproj)).smul contDiff_const

theorem densityProbe_coordinateVector_apply (i j : Fin 3) :
    (coordinateVector i) j = (if j = i then (1 : ℝ) else 0) := by
  simp [coordinateVector, PiLp.single_apply]

theorem densityProbeZ_periodic : IsPeriodicSpatial densityProbeZ := by
  intro x i
  show Real.cos (2 * Real.pi * (x + coordinateVector i) 0) • coordinateVector 0
      = Real.cos (2 * Real.pi * x 0) • coordinateVector 0
  have hadd : (x + coordinateVector i) 0 = x 0 + (if (0 : Fin 3) = i then 1 else 0) := by
    show x 0 + (coordinateVector i) 0 = _
    rw [densityProbe_coordinateVector_apply]
  rcases eq_or_ne (0 : Fin 3) i with hi | hi
  · subst hi
    have hx : (x + coordinateVector (0 : Fin 3)) 0 = x 0 + 1 := by rw [hadd]; norm_num
    have heq : 2 * Real.pi * (x 0 + 1) = 2 * Real.pi * x 0 + 2 * Real.pi := by ring
    rw [hx, heq, Real.cos_add_two_pi]
  · have hx : (x + coordinateVector i) 0 = x 0 := by rw [hadd]; simp [hi]
    rw [hx]

theorem densityProbeZ_integrable :
    Integrable (torusLift densityProbeZ) periodicTorusMeasure :=
  integrable_torusLift_space densityProbeZ_contDiff.continuous

/-- The non-vacuity witness: a nonzero smooth mean-zero periodic field. -/
def densityProbeMZ : SpatialField := meanZeroPartT densityProbeZ

theorem densityProbeMZ_smoothPeriodic : SmoothPeriodicT densityProbeMZ := by
  refine ⟨densityProbeZ_contDiff.sub contDiff_const, ?_⟩
  intro x i
  show densityProbeZ (x + coordinateVector i) - meanT densityProbeZ
      = densityProbeZ x - meanT densityProbeZ
  rw [densityProbeZ_periodic x i]

theorem densityProbeMZ_meanZero : IsMeanZeroT densityProbeMZ :=
  (mean_decomposition densityProbeZ densityProbeZ_periodic densityProbeZ_integrable).2

theorem densityProbeMZ_ne_zero : densityProbeMZ ≠ (0 : SpatialField) := by
  intro h
  set p1 : Space := (2⁻¹ : ℝ) • coordinateVector (0 : Fin 3) with hp1
  have hp1coord : p1 0 = (2⁻¹ : ℝ) := by
    show (2⁻¹ : ℝ) • (coordinateVector (0 : Fin 3)) 0 = (2⁻¹ : ℝ)
    rw [densityProbe_coordinateVector_apply]; simp
  have hp0coord : (0 : Space) 0 = (0 : ℝ) := by simp
  have hzero : densityProbeZ (0 : Space) - densityProbeZ p1 = 0 := by
    have e0 : densityProbeMZ (0 : Space) = 0 := by rw [h]; rfl
    have e1 : densityProbeMZ p1 = 0 := by rw [h]; rfl
    have hd : densityProbeMZ (0 : Space) - densityProbeMZ p1
        = densityProbeZ (0 : Space) - densityProbeZ p1 := by
      simp only [densityProbeMZ, meanZeroPartT]; abel
    rw [e0, e1, sub_zero] at hd
    exact hd.symm
  have hz0 : densityProbeZ (0 : Space) = coordinateVector 0 := by
    show Real.cos (2 * Real.pi * (0 : Space) 0) • coordinateVector 0 = coordinateVector 0
    rw [hp0coord]; simp
  have hz1 : densityProbeZ p1 = (-1 : ℝ) • coordinateVector 0 := by
    show Real.cos (2 * Real.pi * p1 0) • coordinateVector 0 = (-1 : ℝ) • coordinateVector 0
    rw [hp1coord]
    have hpi : 2 * Real.pi * (2⁻¹ : ℝ) = Real.pi := by ring
    rw [hpi, Real.cos_pi]
  rw [hz0, hz1, neg_one_smul, sub_neg_eq_add] at hzero
  have hcv : coordinateVector (0 : Fin 3) ≠ 0 := by
    intro hc
    have hca := densityProbe_coordinateVector_apply 0 0
    rw [hc] at hca
    simp at hca
  have hs : (2 : ℝ) • coordinateVector (0 : Fin 3) = 0 := by rw [two_smul]; exact hzero
  exact hcv ((smul_eq_zero.mp hs).resolve_left (by norm_num))

/-- The witness satisfies the hypothesis of the API field. -/
theorem densityProbeMZ_mem : MemPeriodicHomogeneous (1 / 2) densityProbeMZ :=
  memPeriodicHomogeneous_of_smooth (1 / 2) (by norm_num) densityProbeMZ
    densityProbeMZ_smoothPeriodic densityProbeMZ_meanZero

/-! ## 4. The U4b target instantiated at the nonzero witness: non-vacuous -/

example :
    periodicLpENorm 3 densityProbeMZ
      ≤ ENNReal.ofReal CcriticalHalf * periodicHomogeneousENorm (1 / 2) densityProbeMZ :=
  velocityCriticalL3 densityProbeMZ densityProbeMZ_mem

example : densityProbeMZ ≠ (0 : SpatialField) := densityProbeMZ_ne_zero

end NSFormalization.Section3.T12
