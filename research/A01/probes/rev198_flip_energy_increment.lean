import NSFormalization.Section4.A01.MildEnergyPremises

noncomputable section
namespace NSFormalization.Section4.A01

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift
  EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerSmoothFieldSobolevTime
  EulerQuadraticSource
  EulerVolterraConvolution EulerTimeLp EulerRegularizedTopBlocks
open NSFormalization.Source.ForcedCylinderLocal
open scoped Topology

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

-- Substantive mutation: reverse the signed energy increment in the main conclusion.
example {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (hu : ∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
      (coefficients 1 hq (sobolevPath F hF q))
      (ordinarySobolev (q+1) a.toLp a.translation_contDiff) u t) :
    ∃ U : TimeLp T (SobolevSpace 1 (2+q)),
      Filter.Tendsto (fun n => pathLp T hT (maximalApproximation 1 q T n u))
        Filter.atTop (nhds U) ∧
      ∀ s t (h0s : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T),
        energyRootPath u ⟨s, h0s, hst.trans htT⟩ -
            energyRootPath u ⟨t, h0s.trans hst, htT⟩ ≤
          ∫ r in Icc s t, cylinderEnergyForcing hq hT hTS F hF u U r ∂timeMeasure T := by
  exact mild_energy_estimate_of_cylinder hq hν a ha F hF T hT hTS u hu

end NSFormalization.Section4.A01
