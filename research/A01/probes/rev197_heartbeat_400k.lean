import NSFormalization.Section4.A01.LerayBridge

noncomputable section

namespace NSFormalization.Section4.A01.Review197

open Set
open NSFormalization.Source.ForcedCylinderLocal
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
open EulerSobolevLaplacian EulerSobolevHeatGenerator

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

-- The refactored proof body, rerun at the brief's hard heartbeat ceiling.
set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
theorem residual_difference_gradient_400k {q k m : ℕ} (hq : 6 ≤ q) (hk : 6 ≤ k)
    (hkq : k + 2 ≤ q + 1) (hm : m + 2 ≤ q + 1) (ν : ℝ) {S : ℝ}
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (t : Icc (0 : ℝ) S) :
    value 1 (ComplementPath.unprojectedResidualPath hk hkq ν f u t) -
      value 1 (cylinderResidual hq hm ν f u t) ∈ gradientSpace 1 1 0 := by
  have hv := unprojectedResidual_value hq hk hkq ν f u t
  have hp := cylinderResidual_value hq hm ν f u t
  rw [source_eq] at hp
  change value 1 (cylinderResidual hq hm ν f u t) =
    ν • laplacianEvaluation 1 (q + 1) (by omega) (u t) +
      value 1 (leray 1 q (f t - advection 1 hq (u t) (u t))) at hp
  have he := congrArg₂ (· - ·) hv hp
  rw [add_sub_add_left_eq_sub] at he
  exact he.symm ▸ leray_value_complement_gradient (f t - advection 1 hq (u t) (u t))

end NSFormalization.Section4.A01.Review197
