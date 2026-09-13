import Mathlib
import Formal.ReducedBridgeResidual

namespace MNS2

open Set MeasureTheory
open scoped Interval ContDiff BigOperators

/--
A finite-rank path-tangent approximation with a fixed reference vector `ell` and
scalar coefficient functions `a i` multiplying fixed vectors `phi i`.

This is the abstract form used by POD/modal reduced bridges. It does not assert
that the chosen basis is accurate or that the coefficients can be predicted cheaply.
-/
def finiteRankPath
    {ι Y : Type*} [Fintype ι]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (ell : Y) (a : ι → ℝ → ℝ) (phi : ι → Y) : ℝ → Y :=
  fun s => ell + ∑ i, (a i s) • phi i

/--
If every scalar coefficient is continuous, the finite-rank path is continuous and hence
interval integrable on `[0,1]`.
-/
theorem finiteRankPath_intervalIntegrable
    {ι Y : Type*} [Fintype ι]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (ell : Y) (a : ι → ℝ → ℝ) (phi : ι → Y)
    (ha : ∀ i, Continuous (a i)) :
    IntervalIntegrable (finiteRankPath ell a phi) volume (0 : ℝ) 1 := by
  have hcont : Continuous (finiteRankPath ell a phi) := by
    unfold finiteRankPath
    fun_prop
  exact hcont.intervalIntegrable (μ := volume) (0 : ℝ) 1

/--
The integral of a finite-rank path is the fixed reference plus the same basis vectors
weighted by the integrated scalar coefficients.
-/
theorem intervalIntegral_finiteRankPath
    {ι Y : Type*} [Fintype ι]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (ell : Y) (a : ι → ℝ → ℝ) (phi : ι → Y)
    (ha : ∀ i, Continuous (a i)) :
    (∫ s in (0 : ℝ)..1, finiteRankPath ell a phi s) =
      ell + ∑ i, (∫ s in (0 : ℝ)..1, a i s) • phi i := by
  classical
  unfold finiteRankPath
  rw [intervalIntegral.integral_add]
  · simp only [intervalIntegral.integral_const, sub_zero, one_smul]
    rw [intervalIntegral.integral_finsetSum]
    · have hsum :
          (∑ i, ∫ s in (0 : ℝ)..1, (a i s) • phi i) =
            ∑ i, (∫ s in (0 : ℝ)..1, a i s) • phi i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [intervalIntegral.integral_smul_const]
      rw [hsum]
    · intro i hi
      have hterm : Continuous (fun s : ℝ => (a i s) • phi i) := by
        exact (ha i).smul continuous_const
      exact hterm.intervalIntegrable (μ := volume) (0 : ℝ) 1
  · have hconst : Continuous (fun _ : ℝ => ell) := continuous_const
    exact hconst.intervalIntegrable (μ := volume) (0 : ℝ) 1
  · have hsum : Continuous (fun s : ℝ => ∑ i, (a i s) • phi i) := by
      fun_prop
    exact hsum.intervalIntegrable (μ := volume) (0 : ℝ) 1

/--
Finite-rank specialization of the radial reduced-bridge residual certificate.

The endpoint-difference approximation is written explicitly in terms of the fixed
reference `ell`, fixed basis `phi`, and integrated scalar coefficient functions `a`.
-/
theorem radial_finiteRank_bridge_error_bound
    {ι X Y : Type*} [Fintype ι]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (S : X → Y) (U : Set X) (hU : IsOpen U) (d : X)
    (hS : ContDiffOn ℝ 1 S U)
    (hpath : MapsTo (fun s : ℝ => s • d) (uIcc (0 : ℝ) 1) U)
    (ell : Y) (a : ι → ℝ → ℝ) (phi : ι → Y)
    (ha : ∀ i, Continuous (a i)) :
    ‖(S d - S 0) -
        (ell + ∑ i, (∫ s in (0 : ℝ)..1, a i s) • phi i)‖ ≤
      ∫ s in (0 : ℝ)..1,
        ‖(fderiv ℝ S (s • d)) d - finiteRankPath ell a phi s‖ := by
  have hq := finiteRankPath_intervalIntegrable ell a phi ha
  have hbound := radial_reduced_bridge_error_bound
    (S := S) (U := U) hU (d := d) hS hpath (finiteRankPath ell a phi) hq
  rw [intervalIntegral_finiteRankPath ell a phi ha] at hbound
  exact hbound

/--
Endpoint version of the finite-rank residual certificate when `S 0 = 0` is separately
known.
-/
theorem radial_finiteRank_endpoint_error_bound_of_zero_fixed
    {ι X Y : Type*} [Fintype ι]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (S : X → Y) (U : Set X) (hU : IsOpen U) (d : X)
    (hS : ContDiffOn ℝ 1 S U)
    (hpath : MapsTo (fun s : ℝ => s • d) (uIcc (0 : ℝ) 1) U)
    (hzero : S 0 = 0)
    (ell : Y) (a : ι → ℝ → ℝ) (phi : ι → Y)
    (ha : ∀ i, Continuous (a i)) :
    ‖S d - (ell + ∑ i, (∫ s in (0 : ℝ)..1, a i s) • phi i)‖ ≤
      ∫ s in (0 : ℝ)..1,
        ‖(fderiv ℝ S (s • d)) d - finiteRankPath ell a phi s‖ := by
  simpa [hzero] using
    (radial_finiteRank_bridge_error_bound
      (S := S) (U := U) hU (d := d) hS hpath ell a phi ha)

end MNS2
