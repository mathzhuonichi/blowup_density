import NSFormalization.Section3.T17.ArticleScope

noncomputable section

namespace Review493

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T15
open NSFormalization.Section3.T16 NSFormalization.Section3.T17
open NSFormalization.Section3.T19
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)

variable {ν : ℝ} {u : VelocityField} {p : PressureField} {f : VelocityField}
  {K : Set Space} {place : PlacementData u p f K} {a : SpatialField}
  {g : SpaceTimeField} {r δ : ℝ}
  {reference : ClassicalSolutionT ν a g (place.T + δ)} {D : CutoffData}
  (A : CorrectionAPI ν place (extendByZero reference).velocity r δ D)

include A

/-- Deliberately false proof attempt: mutate the article force-derivative rate
from `ε⁻²⁻ᵐ` to the stronger `ε⁻¹⁻ᵐ`. Lean must reject reuse of the
proved projection because the exponents do not match. -/
example : ∀ m : ℕ,
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ z : SpaceTime,
      ∀ directions : Fin m → Space, (∀ i, ‖directions i‖ ≤ 1) →
        ‖iteratedFDeriv ℝ m
            (correctionForce ν reference.velocity D ε) z
            (fun i => ((0 : ℝ), directions i))‖ ≤
          A.forceDerivConst m * (ε⁻¹) ^ (1 + m) := by
  intro m ε hε
  rw [← article_force_identification A ε hε]
  exact A.force_derivative_bound m ε hε

end Review493
