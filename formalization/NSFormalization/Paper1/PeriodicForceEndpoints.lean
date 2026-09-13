import NSFormalization.Paper1.PeriodicForceConvergence
import NSFormalization.Paper1.PeriodicConcentratedSupport

/-!
# Exact zero-order endpoint for periodized vector forces

For a compactly supported field whose support lies strictly inside the
fundamental cube, the periodic zero-order Fourier energy agrees componentwise
with the whole-space physical `L²` energy.  This is an endpoint identity used
by the scaling layer; it makes no fractional or critical embedding claim.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicForceEndpoints

open Set MeasureTheory NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Paper1
open NSFormalization.Paper1.PeriodicBridge
open NSFormalization.Paper1.LocalizationBoundary
open NSFormalization.Paper1.PeriodicForceConvergence
open NSFormalization.Source
open NavierStokes.PeriodicLocalization NavierStokes.PeriodicIntegration
open scoped ContDiff ENNReal Topology

theorem periodicScalarSobolevSq_zero_periodize_eq
    {r : ℝ} {F : VelocityField} (hF : SupportedInCube r F)
    (hr : r < 1 / 2) (i : Fin 3) {t : ℝ}
    (hreg : ContDiff ℝ 1 (coordinateForce F i))
    (h0 : Integrable (fun x : Space =>
      ‖coordinateForce F i (t, x)‖ ^ 2)) :
    periodicSobolevSq 0
        (fun x => coordinateForce (periodize F) i (t, x)) =
      ∫ x : Space, ‖coordinateForce F i (t, x)‖ ^ 2 := by
  have hcomp : SupportedInCube r (coordinateForce F i) :=
    supported_comp hF (fun v : Space => (v i : ℂ)) (by simp)
  have hcoord : (fun x : Space => coordinateForce (periodize F) i (t, x)) =
      (fun x : Space => periodize (coordinateForce F i) (t, x)) := by
    have hp := periodize_comp hF hr (fun v : Space => (v i : ℂ)) (by simp)
    funext x
    exact congrFun (congrArg (fun H : SpaceTime → ℂ =>
      fun z => H z) hp) (t, x)
  have hperiodic : ContDiff ℝ 1 (fun x =>
      coordinateForce (periodize F) i (t, x)) := by
    rw [hcoord]
    exact (contDiff_periodize hcomp hreg).comp
      (contDiff_const.prodMk contDiff_id)
  have hzero := periodicSobolevSq_zero hperiodic.continuous
  rw [hzero]
  have hnorm : (fun x : Space =>
      ‖coordinateForce (periodize F) i (t, x)‖ ^ 2) =
      (fun x : Space => ‖periodize (coordinateForce F i) (t, x)‖ ^ 2) := by
    funext x
    rw [congrFun hcoord x]
  rw [hnorm]
  exact cubeIntegral_periodize_norm_sq hcomp hr h0

theorem periodicVectorSobolevNorm_zero_periodize_eq
    {r : ℝ} {F : VelocityField} (hF : SupportedInCube r F)
    (hr : r < 1 / 2) {t : ℝ}
    (hreg : ∀ i : Fin 3, ContDiff ℝ 1 (coordinateForce F i))
    (h0 : ∀ i : Fin 3, Integrable (fun x : Space =>
      ‖coordinateForce F i (t, x)‖ ^ 2)) :
    periodicVectorSobolevNorm 0 (periodize F) t =
      Real.sqrt (∑ i : Fin 3, ∫ x : Space,
        ‖coordinateForce F i (t, x)‖ ^ 2) := by
  unfold periodicVectorSobolevNorm
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact periodicScalarSobolevSq_zero_periodize_eq hF hr i (hreg i) (h0 i)

/-- The actual inverse-scale packet inherits the endpoint identity at every
sufficiently small positive scale. Both the support shrinkage and physical
slice integrability follow from compactness and smoothness of the input. -/
theorem eventually_periodicVectorSobolevNorm_zero_periodize_parabolicForce_eq
    {F : VelocityField} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (center : ℝ → ℝ) {t : ℝ}
    (h0 : ∀ ε > 0, ∀ i : Fin 3, Integrable (fun x : Space =>
      ‖coordinateForce (parabolicForce ε⁻¹ (center ε) 0 F) i (t, x)‖ ^ 2)) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      periodicVectorSobolevNorm 0
          (periodize (parabolicForce ε⁻¹ (center ε) 0 F)) t =
        Real.sqrt (∑ i : Fin 3, ∫ x : Space,
          ‖coordinateForce (parabolicForce ε⁻¹ (center ε) 0 F) i (t, x)‖ ^ 2) := by
  filter_upwards [self_mem_nhdsWithin,
      eventually_supportedInQuarterCube_parabolicForce_inv hc center] with ε hpos hε
  have hpos' : 0 < ε := hpos
  apply periodicVectorSobolevNorm_zero_periodize_eq hε (by norm_num)
  · intro i
    exact (coordinateForce_smooth
      (parabolicForce_smooth ε⁻¹ (center ε) 0 hF) i).of_le (by norm_num)
  · intro i
    exact h0 ε hpos' i

end NSFormalization.Paper1.PeriodicForceEndpoints
