import NSFormalization.Section4.A01.AprioriInvariance

noncomputable section

namespace NSFormalization.Section4.A01

open Set EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift
open EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
open EulerSmoothFieldSobolevTime EulerQuadraticSource EulerSobolevHeat EulerVolterraConvolution
open NSFormalization.Source.ForcedCylinderLocal NSFormalization.Source.OrdinaryCylinderDescent
open scoped Topology ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

-- Route β changes the old bound predicate only by adding angle invariance as a premise.
example {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space) (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (R : ℝ) :
    HasAprioriBoundInv hq hν a F hF R ↔
      ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
        (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1))),
        (∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
          (coefficients 1 hq (sobolevPath F hF q))
          (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) →
        (∀ (θ : AddCircle (1 : ℝ)) t,
          sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) → ‖u‖ ≤ R :=
  Iff.rfl

-- The weakened-hypothesis consumer retains the original seven-clause conclusion.
example {q : ℕ} (hq : 6 ≤ q) {ν S R : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (hR : 0 ≤ R)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space) (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (hu₀ : ‖ordinarySobolev (q + 1) a.toLp a.translation_contDiff‖ ≤ R)
    (hbound : HasAprioriBoundInv hq hν a F hF R) :
    ∃ (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
      (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2)),
        ‖u‖ ≤ R ∧
        u ⟨0, le_rfl, hS.le⟩ = ordinarySobolev (q + 1) a.toLp a.translation_contDiff ∧
        U ⟨0, le_rfl, hS.le⟩ = a.toLp ∧
        (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
        (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
        (∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
          (coefficients 1 hq (sobolevPath F hF q))
          (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) ∧
        ∀ (θ : AddCircle (1 : ℝ)) t,
          sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t := by
  exact localTheory_on_prescribed_horizon_of_boundInv hq hν hS hR a ha F hF hu₀ hbound

end NSFormalization.Section4.A01
