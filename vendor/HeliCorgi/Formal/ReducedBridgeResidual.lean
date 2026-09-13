import Mathlib
import Formal.FlowMapLocalContDiff
import Formal.FlowMapOperatorContinuity

namespace MNS2

open Set MeasureTheory
open scoped Interval ContDiff

/--
Bochner interval-integral approximation error on `[0,1]`.

If both the exact integrand `g` and an approximation `q` are interval integrable, then
the norm of the difference of their integrals is bounded by the integral of the pointwise
residual norm.

This theorem is purely analytic. It does not assert that `q` is low rank, POD, modal, or
Navier--Stokes-specific.
-/
theorem interval_integral_approximation_error_bound
    {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (g q : ℝ → Y)
    (hg : IntervalIntegrable g volume (0 : ℝ) 1)
    (hq : IntervalIntegrable q volume (0 : ℝ) 1) :
    ‖(∫ s in (0 : ℝ)..1, g s) - (∫ s in (0 : ℝ)..1, q s)‖ ≤
      ∫ s in (0 : ℝ)..1, ‖g s - q s‖ := by
  rw [← intervalIntegral.integral_sub hg hq]
  apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
  · exact Filter.Eventually.of_forall (fun _ _ => le_rfl)
  · exact (hg.sub hq).norm

/--
Residual certificate for a reduced radial flow-map bridge.

Under the same local open-domain `C¹` assumptions as the exact radial bridge, let `q(s)`
be any interval-integrable approximation to the exact tangent action

`(fderiv ℝ S (s • d)) d`.

Then the error in reconstructing the endpoint difference by integrating `q` is bounded by
the integrated pointwise tangent residual.

No discrete-to-continuum promotion and no low-rank approximation theorem is used here.
-/
theorem radial_reduced_bridge_error_bound
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (S : X → Y) (U : Set X) (hU : IsOpen U) (d : X)
    (hS : ContDiffOn ℝ 1 S U)
    (hpath : MapsTo (fun s : ℝ => s • d) (uIcc (0 : ℝ) 1) U)
    (q : ℝ → Y)
    (hq : IntervalIntegrable q volume (0 : ℝ) 1) :
    ‖(S d - S 0) - (∫ s in (0 : ℝ)..1, q s)‖ ≤
      ∫ s in (0 : ℝ)..1, ‖(fderiv ℝ S (s • d)) d - q s‖ := by
  let J : ℝ → (X →L[ℝ] Y) := fun s => fderiv ℝ S (s • d)
  let g : ℝ → Y := fun s => J s d
  have hfderiv : ContinuousOn (fderiv ℝ S) U :=
    hS.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hpath_cont : ContinuousOn (fun s : ℝ => s • d) (uIcc (0 : ℝ) 1) := by
    fun_prop
  have hJ : ContinuousOn J (uIcc (0 : ℝ) 1) := by
    exact hfderiv.comp hpath_cont hpath
  have hg_cont : ContinuousOn g (uIcc (0 : ℝ) 1) := by
    exact continuousOn_clm_apply_fixed J d hJ
  have hg : IntervalIntegrable g volume (0 : ℝ) 1 :=
    hg_cont.intervalIntegrable
  have hbridge : (∫ s in (0 : ℝ)..1, g s) = S d - S 0 := by
    simpa [g, J] using
      (radial_flowmap_bridge_of_contDiffOn_open
        (S := S) (U := U) hU (d := d) hS hpath)
  rw [← hbridge]
  simpa [g, J] using interval_integral_approximation_error_bound g q hg hq

/--
Endpoint version of `radial_reduced_bridge_error_bound` when the zero datum is known
to evolve to the zero state.
-/
theorem radial_reduced_endpoint_error_bound_of_zero_fixed
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (S : X → Y) (U : Set X) (hU : IsOpen U) (d : X)
    (hS : ContDiffOn ℝ 1 S U)
    (hpath : MapsTo (fun s : ℝ => s • d) (uIcc (0 : ℝ) 1) U)
    (hzero : S 0 = 0)
    (q : ℝ → Y)
    (hq : IntervalIntegrable q volume (0 : ℝ) 1) :
    ‖S d - (∫ s in (0 : ℝ)..1, q s)‖ ≤
      ∫ s in (0 : ℝ)..1, ‖(fderiv ℝ S (s • d)) d - q s‖ := by
  simpa [hzero] using
    (radial_reduced_bridge_error_bound
      (S := S) (U := U) hU (d := d) hS hpath q hq)

end MNS2
