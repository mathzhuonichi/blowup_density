import NSFormalization.Section4.A01.CommonHorizon

noncomputable section
namespace NSFormalization.Section4.A01

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift
open EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
open EulerSmoothFieldSobolevTime EulerQuadraticSource EulerSobolevHeat EulerVolterraConvolution
open NSFormalization.Source.ForcedCylinderLocal NSFormalization.Source.OrdinaryCylinderDescent
open scoped Topology ContDiff NNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/- Deliberate mutation: the conclusion uses the negative of the canonical
   lower-order force.  The genuine lowering theorem must not prove this. -/
example {p q : ℕ} (hp : 6 ≤ p) (hq : 6 ≤ q) (h : q ≤ p)
    {ν S : ℝ} (hν : 0 < ν) (hS : 0 ≤ S) (a : SmoothL2Field Space)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (p+1)))
    (hu : ∀ t, u t = quadraticDuhamel 1 ν hν hS le_rfl
      (coefficients 1 hp (sobolevPath F hF p))
      (ordinarySobolev (p+1) a.toLp a.translation_contDiff) u t) :
    let v := (restrictOperator 1 (Nat.succ_le_succ h)).compLeftContinuous ℝ _ u
    ∀ t, v t = quadraticDuhamel 1 ν hν hS le_rfl
      (coefficients 1 hq (-(sobolevPath F hF q)))
      (ordinarySobolev (q+1) a.toLp a.translation_contDiff) v t := by
  exact lower_forced_mild hp hq h hν hS a F hF u hu

end NSFormalization.Section4.A01
