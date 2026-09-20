import NSFormalization.Section4.A01.AprioriFamily

noncomputable section
namespace NSFormalization.Section4.A01.Rev193

open Set EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift
open EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
open EulerSmoothFieldSobolevTime EulerQuadraticSource
open NSFormalization.Source.ForcedCylinderLocal
open scoped Topology ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/- Substantive mutation: strengthen the proved exponential radius by replacing the
sharp transferred factor `256` with `255`. The direct proof from `hb_of_base`
must fail at the conclusion's radius. -/
def mutatedRadius255 {S : ℝ} (a : SmoothL2Field Space)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (R₆ : ℝ) (E C : ℕ → ℝ) (q : ℕ) : ℝ :=
  E q * (‖ordinarySobolev (q+1) a.toLp a.translation_contDiff‖ +
    S * ‖sobolevPath F hF (q+1)‖) * Real.exp (C q * (255 * R₆^2 * S))

theorem mutated_hb_of_base_255 {ν S R₆ : ℝ} (hν : 0 < ν) (hS : 0 ≤ S)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (u₆ : C(Icc (0 : ℝ) S, SobolevSpace 1 7)) (hR : ‖u₆‖ ≤ R₆)
    (h₆ : ∀ t, u₆ t = quadraticDuhamel 1 ν hν hS le_rfl
      (coefficients 1 (le_refl 6) (sobolevPath F hF 6))
      (ordinarySobolev 7 a.toLp a.translation_contDiff) u₆ t)
    (E C : ℕ → ℝ) (hE : ∀ q, 0 ≤ E q) (hC : ∀ q, 0 ≤ C q)
    (hMG : ∀ q (hq : 6 ≤ q), MildGronwall hq hν a ha F hF (E q) (C q)) :
    ∀ q (hq : 6 ≤ q), HasAprioriBound hq hν a F hF
      (mutatedRadius255 a F hF R₆ E C q) := by
  exact hb_of_base hν hS a ha F hF u₆ hR h₆ E C hE hC hMG

end NSFormalization.Section4.A01.Rev193
