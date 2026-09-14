import NSFormalization.Section4.A01.L2Descent

/-! Reviewer probe (lane 153) — lane 151's two order-restricted results are now strictly subsumed by
lane 153's, so nothing in `CarrierWords.lean` is still needed for `hword_jet` (a simplifier note, not
a blocker: `word_descent_ae` / `word_descent_ae_partial` / `hword_jet_of_descent` remain in the tree
as the `n + 3 ≤ q + 1` special cases). -/

noncomputable section
namespace Rev153Subsumes

open MeasureTheory
open NavierStokes.ProblemStatement (Space coordinateVector)
open NSFormalization.Section4.A01
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace EulerCylinderSobolev
open EulerLpTranslation
open scoped ENNReal ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

variable {q : ℕ} (u : SobolevSpace 1 (q + 1))
  (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u = u)
  (U : EulerMeanSolenoidal.L2) (hU : ordinaryLift U = value 1 u)
  (Z : SmoothL2Field Space) (hUz : (⇑U) =ᵐ[volume] Z.field)

/-- 151's `hword_jet_of_descent` is 153's `hword_jet_full` restricted. -/
example : ∀ (n : ℕ) (hn : n + 3 ≤ q + 1) (w : Fin n → Fin 4),
    ‖word 1 u (by omega) w‖ ≤ (eLpNorm (iteratedFDeriv ℝ n Z.field) 2 volume).toReal :=
  fun n hn w => hword_jet_full u hu U hU Z hUz n (by omega) w

/-- 151's `word_descent_ae` is 153's `word_descent_ae_full` restricted. -/
example : ∀ (n : ℕ) (hn : n + 3 ≤ q + 1) (w : Fin n → Fin 3) (Zw : EulerMeanSolenoidal.L2),
    ordinaryLift Zw = word 1 u (by omega) (fun i => (w i).succ) →
    (⇑Zw) =ᵐ[volume] (wordField Z w).field :=
  fun n hn w Zw hZw => word_descent_ae_full u hu U hU Z hUz n (by omega) w Zw hZw

/-- The three top orders lane 151 could NOT reach are now real bounds: `n = q + 1`. -/
example (w : Fin (q + 1) → Fin 4) :
    ‖word 1 u le_rfl w‖ ≤ (eLpNorm (iteratedFDeriv ℝ (q + 1) Z.field) 2 volume).toReal :=
  hword_jet_full u hu U hU Z hUz (q + 1) le_rfl w

end Rev153Subsumes
