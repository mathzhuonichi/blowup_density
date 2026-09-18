import NSFormalization.Section3.T12.GradientLSix

/-!
# Lane 400 probe: the `gradientLSix` field of `MeanZeroSobolevCalculusAPI` closes

The first section copies the field `gradientLSix` of
`research/T12/probes/api_on_canonical.lean:184-187` verbatim, with the API data
field `Csix` replaced by the explicit constant `Csix` of
`NSFormalization/Section3/T12/GradientLSix.lean`, and closes it by `exact`.
The second section exhibits the intermediate estimates of the route.  The third
section instantiates the field at a nonzero smooth mean-zero periodic field (the
single cosine mode `x ↦ cos(2π x₀)·e₀` made mean-free, the witness of
`research/T12/probes/cutoff_gagliardo_closes.lean`), so neither the hypotheses
nor the conclusion is vacuous.
-/

noncomputable section

namespace NSFormalization.Section3.T12

open Set MeasureTheory Metric
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section4.A05 (dirDeriv lap gradTensor SmoothL2)
open scoped ContDiff ENNReal BigOperators Real

/-! ## 1. The API field, verbatim -/

/-- `gradientLSix`, with `Csix := NSFormalization.Section3.T12.Csix`. -/
example :
    ∀ v : SpatialField, SmoothPeriodicT v → IsMeanZeroT v →
      periodicLpENorm 6 (gradientTensor v) ≤
        ENNReal.ofReal Csix * periodicLpENorm 2 (laplacian v) :=
  gradientLSix

/-- `Csix_pos`. -/
example : 0 < Csix := Csix_pos

/-! ## 2. The intermediate estimates of route (c) -/

/-- Leibniz for the localization `χv`. -/
example {v : SpatialField} (hv : ContDiff ℝ ∞ v) (x : Space) :
    lap (cutoffMul v) x
      = cutoff x • lap v x
        + (∑ i : Fin 3, ((dirDeriv i cutoff x) • dirDeriv i v x
            + (dirDeriv i cutoff x) • dirDeriv i v x))
        + (lap cutoff x) • v x :=
  lap_cutoffMul_eq hv x

/-- The pointwise majorant of the localized Laplacian. -/
example {v : SpatialField} (hv : ContDiff ℝ ∞ v) (x : Space) :
    ‖lap (cutoffMul v) x‖
      ≤ leibnizConst * (‖lap v x‖ + ‖gradTensor v x‖ + ‖v x‖) :=
  norm_lap_cutoffMul_le hv x

/-- The lattice tiling bound, with the lane-377 count `7³ = 343`. -/
example {v : SpatialField} (hv : SmoothPeriodicT v) :
    eLpNorm (lap (cutoffMul v)) 2 volume
      ≤ 343 * eLpNorm (leibnizMajorant v) 2 (volume.restrict fundamentalCube) :=
  eLpNorm_lap_cutoffMul_le hv

/-- The registered whole-space embedding applies to `χv`. -/
example {v : SpatialField} (hv : ContDiff ℝ ∞ v) : SmoothL2 (cutoffMul v) :=
  smoothL2_cutoffMul hv

/-- The two torus lower-order bounds. -/
example {v : SpatialField} (hv : SmoothPeriodicT v) (hm : IsMeanZeroT v) :
    periodicLpENorm 2 v ≤ ENNReal.ofReal hTwoConst * periodicLpENorm 2 (laplacian v) :=
  periodicLpENorm_two_le_laplacian hv hm

example {v : SpatialField} (hv : SmoothPeriodicT v) (hm : IsMeanZeroT v) :
    periodicLpENorm 2 (gradientTensor v)
      ≤ ENNReal.ofReal hTwoConst * periodicLpENorm 2 (laplacian v) :=
  periodicLpENorm_gradientTensor_le_laplacian hv hm

/-! ## 3. A genuine nonzero smooth mean-zero periodic witness

Copied from `research/T12/probes/cutoff_gagliardo_closes.lean` (lane 377):
`probeZ x = cos(2π x₀)·e₀`, and `probeMZ = meanZeroPartT probeZ` is nonzero,
smooth, periodic and mean-zero. -/

/-- A single-mode cosine vector field, `x ↦ cos(2π x₀)·e₀`. -/
def probeZ : SpatialField := fun x => Real.cos (2 * Real.pi * x 0) • coordinateVector 0

theorem probeZ_contDiff : ContDiff ℝ ∞ probeZ := by
  unfold probeZ
  have hproj : ContDiff ℝ ∞ (fun x : Space => x 0) := contDiff_piLp_apply 2
  exact (Real.contDiff_cos.comp (contDiff_const.mul hproj)).smul contDiff_const

theorem coordinateVector_apply (i j : Fin 3) :
    (coordinateVector i) j = (if j = i then (1 : ℝ) else 0) := by
  simp [coordinateVector, PiLp.single_apply]

theorem probeZ_periodic : IsPeriodicSpatial probeZ := by
  intro x i
  show Real.cos (2 * Real.pi * (x + coordinateVector i) 0) • coordinateVector 0
      = Real.cos (2 * Real.pi * x 0) • coordinateVector 0
  have hadd : (x + coordinateVector i) 0 = x 0 + (if (0 : Fin 3) = i then 1 else 0) := by
    show x 0 + (coordinateVector i) 0 = _
    rw [coordinateVector_apply]
  rcases eq_or_ne (0 : Fin 3) i with hi | hi
  · subst hi
    have hx : (x + coordinateVector (0 : Fin 3)) 0 = x 0 + 1 := by rw [hadd]; norm_num
    have heq : 2 * Real.pi * (x 0 + 1) = 2 * Real.pi * x 0 + 2 * Real.pi := by ring
    rw [hx, heq, Real.cos_add_two_pi]
  · have hx : (x + coordinateVector i) 0 = x 0 := by rw [hadd]; simp [hi]
    rw [hx]

theorem probeZ_integrable : Integrable (torusLift probeZ) periodicTorusMeasure :=
  integrable_torusLift_space probeZ_contDiff.continuous

/-- The non-vacuity witness: a nonzero smooth mean-zero periodic field. -/
def probeMZ : SpatialField := meanZeroPartT probeZ

theorem probeMZ_smoothPeriodic : SmoothPeriodicT probeMZ := by
  refine ⟨probeZ_contDiff.sub contDiff_const, ?_⟩
  intro x i
  show probeZ (x + coordinateVector i) - meanT probeZ = probeZ x - meanT probeZ
  rw [probeZ_periodic x i]

theorem probeMZ_meanZero : IsMeanZeroT probeMZ :=
  (mean_decomposition probeZ probeZ_periodic probeZ_integrable).2

theorem probeMZ_ne_zero : probeMZ ≠ (0 : SpatialField) := by
  intro h
  set p1 : Space := (2⁻¹ : ℝ) • coordinateVector (0 : Fin 3) with hp1
  have hp1coord : p1 0 = (2⁻¹ : ℝ) := by
    show (2⁻¹ : ℝ) • (coordinateVector (0 : Fin 3)) 0 = (2⁻¹ : ℝ)
    rw [coordinateVector_apply]; simp
  have hp0coord : (0 : Space) 0 = (0 : ℝ) := by simp
  have hzero : probeZ (0 : Space) - probeZ p1 = 0 := by
    have e0 : probeMZ (0 : Space) = 0 := by rw [h]; rfl
    have e1 : probeMZ p1 = 0 := by rw [h]; rfl
    have hd : probeMZ (0 : Space) - probeMZ p1 = probeZ (0 : Space) - probeZ p1 := by
      simp only [probeMZ, meanZeroPartT]; abel
    rw [e0, e1, sub_zero] at hd
    exact hd.symm
  have hz0 : probeZ (0 : Space) = coordinateVector 0 := by
    show Real.cos (2 * Real.pi * (0 : Space) 0) • coordinateVector 0 = coordinateVector 0
    rw [hp0coord]; simp
  have hz1 : probeZ p1 = (-1 : ℝ) • coordinateVector 0 := by
    show Real.cos (2 * Real.pi * p1 0) • coordinateVector 0 = (-1 : ℝ) • coordinateVector 0
    rw [hp1coord]
    have hpi : 2 * Real.pi * (2⁻¹ : ℝ) = Real.pi := by ring
    rw [hpi, Real.cos_pi]
  rw [hz0, hz1, neg_one_smul, sub_neg_eq_add] at hzero
  have hcv : coordinateVector (0 : Fin 3) ≠ 0 := by
    intro hc
    have hca := coordinateVector_apply 0 0
    rw [hc] at hca
    simp at hca
  have hs : (2 : ℝ) • coordinateVector (0 : Fin 3) = 0 := by rw [two_smul]; exact hzero
  exact hcv ((smul_eq_zero.mp hs).resolve_left (by norm_num))

/-- The `gradientLSix` field instantiated at the nonzero witness: non-vacuous. -/
example :
    periodicLpENorm 6 (gradientTensor probeMZ) ≤
      ENNReal.ofReal Csix * periodicLpENorm 2 (laplacian probeMZ) :=
  gradientLSix probeMZ probeMZ_smoothPeriodic probeMZ_meanZero

example : probeMZ ≠ (0 : SpatialField) := probeMZ_ne_zero

end NSFormalization.Section3.T12
