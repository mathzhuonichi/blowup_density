import NSFormalization.Section4.A01.AprioriInvariance

noncomputable section

namespace NSFormalization.Section4.A01

open Set EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift
open EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
open EulerSmoothFieldSobolevTime EulerQuadraticSource EulerSobolevHeat EulerVolterraConvolution
open NSFormalization.Source.ForcedCylinderLocal NSFormalization.Source.OrdinaryCylinderDescent
open scoped Topology ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

-- Deliberate substantive mutation: strengthen the main output bound from R to R - 1.
example {q : ℕ} (hq : 6 ≤ q) {ν S R : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (hR : 0 ≤ R)
    (a : SmoothL2Field Space)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space) (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (hu₀ : ‖ordinarySobolev (q + 1) a.toLp a.translation_contDiff‖ ≤ R)
    (hbound : HasAprioriBoundInv hq hν a F hF R) :
    ∃ u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)),
      ‖u‖ ≤ R - 1 ∧
      u ⟨0, le_rfl, hS.le⟩ = ordinarySobolev (q + 1) a.toLp a.translation_contDiff ∧
      (∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
        (coefficients 1 hq (sobolevPath F hF q))
        (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) ∧
      ∀ (θ : AddCircle (1 : ℝ)) t,
        sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t := by
  obtain ⟨u, hu, hi, hm, hinv⟩ :=
    forced_global_mild_of_boundInv hq hν hS hR a F hF hu₀ hbound
  exact ⟨u, hu, hi, hm, hinv⟩

end NSFormalization.Section4.A01
