import NSFormalization.Section3.T12.GradientLambdaL3

/-!
# U6 closure probe (lane 405)

`gradientLambdaCriticalL3` (the T12 U6 order-`3/2` sum embedding) is proved in
`Section3/T12/GradientLambdaL3.lean`.  This probe:

* closes the API field `gradientLambdaCriticalL3` of
  `research/T12/probes/api_on_canonical.lean:170-175` **verbatim** by `exact`
  (same binders, same order, same left- and right-hand sides, constant
  `CcriticalThreeHalves`);
* records the explicit positive constant and the two Fourier order-shift
  comparisons it is built from;
* instantiates the field on the genuine nonzero smooth mean-zero periodic
  witness `probeMZ = meanZeroPartT (x ↦ cos(2π x₀)·e₀)` (lane 377/396's witness,
  reproduced here since research probes cannot import one another) together with
  the `Λ`-representative supplied by `lambda_exists`, so neither the hypotheses
  nor the conclusion is vacuous.
-/

noncomputable section

namespace NSFormalization.Section3.T12

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section4.A05 (dirDeriv)
open scoped ContDiff ENNReal BigOperators Real

/-! ## 1. The API field, verbatim -/

example :
    ∀ (v Lv : SpatialField), SmoothPeriodicT v →
      MemPeriodicHomogeneous (3 / 2) v → IsPeriodicLambda v Lv →
        periodicLpENorm 3 (gradientTensor v) + periodicLpENorm 3 Lv ≤
          ENNReal.ofReal CcriticalThreeHalves *
            periodicHomogeneousENorm (3 / 2) v :=
  gradientLambdaCriticalL3

example : 0 < CcriticalThreeHalves := CcriticalThreeHalves_pos

/-! ## 2. The two order-shift comparisons and the column assembly -/

example (v : SpatialField) (hv : SmoothPeriodicT v) (j : Fin 3) :
    periodicHomogeneousENorm (1 / 2) (dirDeriv j v) ≤
      periodicHomogeneousENorm (3 / 2) v :=
  homogeneousENorm_half_dirDeriv_le v hv j

example (v Lv : SpatialField) (hL : IsPeriodicLambda v Lv) :
    periodicHomogeneousENorm (1 / 2) Lv ≤ periodicHomogeneousENorm (3 / 2) v :=
  homogeneousENorm_half_lambda_le v Lv hL

example (v : SpatialField) (hv : SmoothPeriodicT v) :
    periodicLpENorm 3 (gradientTensor v) ≤
      ∑ j : Fin 3, periodicLpENorm 3 (dirDeriv j v) :=
  periodicLpENorm_gradientTensor_le_sum v hv (by norm_num)

example (k : PeriodicFrequency) :
    homogeneousDatumWeight (3 / 2) k =
      homogeneousDatumWeight (1 / 2) k * Real.sqrt (periodicAngularFrequencySq k) :=
  homogeneousDatumWeight_three_halves k

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

/-! ## 4. The U6 target instantiated at the nonzero witness: non-vacuous -/

theorem probeMZ_mem : MemPeriodicHomogeneous (3 / 2) probeMZ :=
  ⟨probeMZ_smoothPeriodic.2,
    memLp_torusLift_vector probeMZ_smoothPeriodic.1.continuous 2,
    probeMZ_meanZero,
    ne_of_lt (NSFormalization.Section3.T13.periodicHomogeneousENorm_lt_top
      (by norm_num) probeZ_periodic probeZ_contDiff)⟩

example : ∃ Lv : SpatialField, IsPeriodicLambda probeMZ Lv ∧
    periodicLpENorm 3 (gradientTensor probeMZ) + periodicLpENorm 3 Lv ≤
      ENNReal.ofReal CcriticalThreeHalves * periodicHomogeneousENorm (3 / 2) probeMZ := by
  obtain ⟨Lv, hLv⟩ := lambda_exists probeMZ probeMZ_smoothPeriodic
  exact ⟨Lv, hLv,
    gradientLambdaCriticalL3 probeMZ Lv probeMZ_smoothPeriodic probeMZ_mem hLv⟩

example : probeMZ ≠ (0 : SpatialField) := probeMZ_ne_zero

end NSFormalization.Section3.T12
