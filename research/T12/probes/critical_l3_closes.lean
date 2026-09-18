import NSFormalization.Section3.T12.CriticalL3

/-!
# U4 closure probe (lane 396)

The T12 U4 mean-zero torus critical embedding (smooth form) `velocityCriticalL3_smooth`
is proved in `Section3/T12/CriticalL3.lean`.  This probe:

* closes the API field statement `velocityCriticalL3` **under the smoothness its two
  analytic inputs require** (`SmoothPeriodicT v ∧ IsMeanZeroT v`), verbatim in the LHS
  `periodicLpENorm 3 v` and RHS `ENNReal.ofReal CcriticalHalf · periodicHomogeneousENorm
  (1/2) v`;
* records the explicit positive constant and the homogeneous-norm spelling bridge;
* instantiates the theorem on the genuine nonzero smooth mean-zero periodic witness
  `probeMZ = meanZeroPartT (x ↦ cos(2π x₀)·e₀)` (lane 377's witness, reproduced here since
  research probes cannot import one another), so neither hypotheses nor conclusion is
  vacuous.

The general `MemPeriodicHomogeneous (1/2)` field of the API is the density residual
documented in `research/T12/ATTEMPTS_U4.md`.
-/

noncomputable section

namespace NSFormalization.Section3.T12

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section4.D01 (dotHomogeneousENorm)
open scoped ContDiff ENNReal BigOperators Real

/-! ## 1. The API field, verbatim, under the smoothness the inputs require -/

example (v : SpatialField) (hv : SmoothPeriodicT v) (hmean : IsMeanZeroT v) :
    periodicLpENorm 3 v
      ≤ ENNReal.ofReal CcriticalHalf * periodicHomogeneousENorm (1 / 2) v :=
  velocityCriticalL3_smooth v hv hmean

example : 0 < CcriticalHalf := CcriticalHalf_pos

/-- The homogeneous-norm spelling bridge used at the A05 application. -/
example : NSFormalization.Section4.A05.dotHomogeneousENorm = dotHomogeneousENorm :=
  a05_dotHomogeneousENorm_eq

/-! ## 2. Supporting facts used in the reduction -/

example (v : SpatialField) (hv : SmoothPeriodicT v)
    (hmem : MemPeriodicHomogeneous (1 / 2) v) :
    eLpNorm v 2 (volume.restrict fundamentalCube)
      ≤ ENNReal.ofReal (gapConst (1 / 2)) * periodicHomogeneousENorm (1 / 2) v :=
  l2Q_le_homogeneous_half v hv hmem

example (v : SpatialField) :
    periodicSobolevENorm 0 v ≤ periodicSobolevENorm (1 / 2) v :=
  periodicSobolevENorm_zero_le_half v

/-! ## 3. A genuine nonzero smooth mean-zero periodic witness (lane 377's `probeMZ`) -/

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

/-! ## 4. The U4 target instantiated at the nonzero witness: non-vacuous -/

example :
    periodicLpENorm 3 probeMZ
      ≤ ENNReal.ofReal CcriticalHalf * periodicHomogeneousENorm (1 / 2) probeMZ :=
  velocityCriticalL3_smooth probeMZ probeMZ_smoothPeriodic probeMZ_meanZero

example : probeMZ ≠ (0 : SpatialField) := probeMZ_ne_zero

end NSFormalization.Section3.T12
