import NSFormalization.Section4.A04.H1Bridges
import NSFormalization.Section3.T11.H1Bridges

/-! Consumer-shaped closure probes for P21 Route B unit B0. -/

noncomputable section

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.A02
open NSFormalization.Section3.T10
open NSFormalization.Section3.T12 (periodicLpENorm)
open scoped ContDiff ENNReal

namespace NSFormalization.Research.P21.B0Probes

example {z : SpatialField} (hz : ContDiff ℝ ∞ z) (hc : HasCompactSupport z) :
    (Section4.D01.sobolevENorm 1 z).toReal ^ 2 =
      Section4.A04.l2EnergyR z + Section4.A04.gradientEnergyR z :=
  Section4.A04.sobolevENorm_one_toReal_sq_eq hz hc

example {z : SpatialField} (hz : ContDiff ℝ ∞ z) (hc : HasCompactSupport z) :
    (Section4.D01.sobolevENorm 2 z).toReal ^ 2 =
      (Section4.D01.sobolevENorm 1 z).toReal ^ 2 +
        Section4.A04.gradientEnergyR z + Section4.A04.hessianEnergyR z :=
  Section4.A04.sobolevENorm_two_eq_one_add_gradient_hessian hz hc

example {f : SpaceTimeField} (hf : MemForceR f) {S : ℝ} (hS : 0 ≤ S) :
    Section4.A04.forceL2CapR f S ≠ ⊤ :=
  Section4.A04.forceL2CapR_ne_top hf hS

example {f : SpaceTimeField} {S t₀ t : ℝ}
    (ht₀ : t₀ ∈ Icc (0 : ℝ) S) (ht : t ∈ Icc (0 : ℝ) 1) :
    eLpNorm (fun x : Space => Section4.A04.timeShift t₀ f (t, x)) 2 volume ≤
      Section4.A04.forceL2CapR f S :=
  Section4.A04.timeShift_force_slice_le_forceL2CapR ht₀ ht

example {z : SpatialField} (hz : ContDiff ℝ ∞ z) (hp : IsPeriodicSpatial z) :
    (periodicSobolevENorm 1 z).toReal ^ 2 =
      Section3.T11.periodicL2Energy z + Section3.T11.periodicGradientEnergy z :=
  Section3.T11.periodicSobolevENorm_one_toReal_sq_eq hz hp

example {z : SpatialField} (hz : ContDiff ℝ ∞ z) (hp : IsPeriodicSpatial z) :
    (periodicSobolevENorm 2 z).toReal ^ 2 =
      (periodicSobolevENorm 1 z).toReal ^ 2 +
        Section3.T11.periodicGradientEnergy z + Section3.T11.periodicHessianEnergy z :=
  Section3.T11.periodicSobolevENorm_two_eq_one_add_gradient_hessian hz hp

example {f : SpaceTimeField} (hf : MemForceT f) {S : ℝ} (hS : 0 ≤ S) :
    Section3.T11.forceL2CapT f S ≠ ⊤ :=
  Section3.T11.forceL2CapT_ne_top hf hS

example {f : SpaceTimeField} {S t₀ t : ℝ}
    (ht₀ : t₀ ∈ Icc (0 : ℝ) S) (ht : t ∈ Icc (0 : ℝ) 1) :
    periodicLpENorm 2 (fun x : Space => Section3.T11.timeShiftT t₀ f (t, x)) ≤
      Section3.T11.forceL2CapT f S :=
  Section3.T11.timeShiftT_force_slice_le_forceL2CapT ht₀ ht

example {f : SpaceTimeField} (hf : MemForceT f) (t₀ : ℝ) :
    ContDiff ℝ ∞ (Section3.T11.timeShiftT t₀ f) ∧
      IsPeriodicOn univ (Section3.T11.timeShiftT t₀ f) :=
  Section3.T11.timeShiftT_smooth_periodic hf t₀

end NSFormalization.Research.P21.B0Probes
