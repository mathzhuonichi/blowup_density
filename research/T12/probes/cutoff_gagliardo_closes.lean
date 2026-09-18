import NSFormalization.Section3.T12.CutoffGagliardo

/-!
# U3 closure probe (lane 377)

The T12 U3 analytic core `cutoff_gagliardo_half` is proved in
`Section3/T12/CutoffGagliardo.lean`.  This probe closes it verbatim, exhibits
the two localization kernel bounds and the reduction backbone, and instantiates
the theorem on a genuine nonzero smooth mean-zero periodic field (the single
cosine mode `x ↦ cos(2π x₀)·e₀`, made mean-zero by `meanZeroPartT`), so neither
the hypotheses nor the conclusion is vacuous.
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

/-! ## 1. The U3 target, verbatim -/

example (v : SpatialField) (hv : SmoothPeriodicT v) (hmean : IsMeanZeroT v) :
    dotHomogeneousENorm (1 / 2) (cutoffMul v)
      ≤ ENNReal.ofReal cutoffGagliardoConst
        * (eLpNorm v 2 (volume.restrict fundamentalCube)
            + periodicHomogeneousENorm (1 / 2) v) :=
  cutoff_gagliardo_half v hv hmean

example : 0 < cutoffGagliardoConst := cutoffGagliardoConst_pos

/-! ## 2. The two localization kernel bounds and the difference split -/

example {v : SpatialField} (hv : SmoothPeriodicT v) :
    IA v ≤ ENNReal.ofReal 343 * ITorus (1 / 2) v := iA_bound hv

example {v : SpatialField} (hv : SmoothPeriodicT v) :
    IB v ≤ ENNReal.ofReal cbConst
      * eLpNorm v 2 (volume.restrict fundamentalCube) ^ 2 := iB_bound hv

example {v : SpatialField} (hv : SmoothPeriodicT v) :
    IReal (1 / 2) (cutoffMul v) ≤ 2 * IA v + 2 * IB v := ireal_cutoffMul_le_split hv

/-! ## 3. The two Gagliardo identities at `s = 1/2`, verbatim -/

example {v : SpatialField} (hv : SmoothPeriodicT v) :
    IReal (1 / 2) (cutoffMul v)
      = cFrac (1 / 2) * dotHomogeneousENorm (1 / 2) (cutoffMul v) ^ (2 : ℕ) :=
  ireal_cutoffMul_eq hv

example {v : SpatialField} (hv : SmoothPeriodicT v) (hm : IsMeanZeroT v) :
    ITorus (1 / 2) v
      = cFrac (1 / 2) * periodicHomogeneousENorm (1 / 2) v ^ (2 : ℕ) :=
  itorus_meanZero_eq hv hm

/-! ## 4. A genuine nonzero smooth mean-zero periodic witness

`probeZ x = cos(2π x₀)·e₀`; `probeMZ = meanZeroPartT probeZ` is nonzero,
smooth, periodic, and mean-zero, so the U3 target is non-vacuous. -/

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

/-- The U3 target instantiated at the nonzero witness: non-vacuous. -/
example :
    dotHomogeneousENorm (1 / 2) (cutoffMul probeMZ)
      ≤ ENNReal.ofReal cutoffGagliardoConst
        * (eLpNorm probeMZ 2 (volume.restrict fundamentalCube)
            + periodicHomogeneousENorm (1 / 2) probeMZ) :=
  cutoff_gagliardo_half probeMZ probeMZ_smoothPeriodic probeMZ_meanZero

example : probeMZ ≠ (0 : SpatialField) := probeMZ_ne_zero

end NSFormalization.Section3.T12
