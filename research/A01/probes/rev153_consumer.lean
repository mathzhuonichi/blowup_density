import NSFormalization.Section4.A01.L2Descent

/-! Reviewer probe (lane 153) — `hword_jet_full` actually discharges the named hypothesis
`hword_jet` of `AprioriRows.sobolevSpace_norm_le_sobolevENorm` (`AprioriRows.lean:287-291`) at
`z := Z.field`, giving the converse norm comparison with no `hword_jet` gap left. -/

noncomputable section
namespace Rev153Consumer

open MeasureTheory
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Section4.D01
open NSFormalization.Section4.A01
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace EulerCylinderSobolev
open EulerLpTranslation
open scoped ENNReal ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- The converse norm comparison, with `hword_jet` gone. -/
theorem converse_no_hword_jet {q : ℕ} (u : SobolevSpace 1 (q + 1))
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u = u)
    (U : EulerMeanSolenoidal.L2) (hU : ordinaryLift U = value 1 u)
    (Z : SmoothL2Field Space) (hUz : (⇑U) =ᵐ[volume] Z.field)
    (hfin : sobolevENorm ((q + 1 : ℕ) : ℝ) Z.field ≠ ⊤) :
    ‖u‖ ≤ jetSobolevConst (q + 1) * (sobolevENorm ((q + 1 : ℕ) : ℝ) Z.field).toReal :=
  sobolevSpace_norm_le_sobolevENorm u Z.smooth hfin (hword_jet_full u hu U hU Z hUz)

#print axioms converse_no_hword_jet

end Rev153Consumer
