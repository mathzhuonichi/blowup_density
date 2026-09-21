import NSFormalization.Section4.A01.ForcingFamilyBound
import NSFormalization.Section4.A01.SignedLimit

namespace NSFormalization.Section4.A01

open Set EulerSmoothLimit EulerLpTranslation

example {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (hFB : ForcingFamilyBound hq hν a F hF (E q) (A q))
    (hpass : CylinderSignedEnergyPassage hq hν a ha F hF) :
    CylinderSignedRootLimit hq hν a ha F hF (E q) (A q) := by
  exact cylinderSignedRootLimit_of_forcingBound hq hν a ha F hF
    (mul_nonneg (E_nonneg q) (norm_nonneg _)) hFB hpass

example {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (hFB : ForcingFamilyBound hq hν a F hF (E q) (A q))
    (hpass : CylinderSignedEnergyPassage hq hν a ha F hF) :
    FiniteMildEnergy hq hν a ha F hF (E q) (A q) := by
  exact finiteMildEnergy_of_forcingBound' hq hν a ha F hF le_rfl hFB hpass

end NSFormalization.Section4.A01
