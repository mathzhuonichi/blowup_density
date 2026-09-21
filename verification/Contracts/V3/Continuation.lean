import Contracts.V2.Continuation
import Contracts.V2.LocalTheory

/-!
# Whole-space continuation V3

This version adds the two fixed-force H¹-uniform statements while reusing all
registered V1/V2 vocabulary.  `A04.continuation_v2` remains separately
registered for its H⁷ restart and integral-continuation routes.
-/

noncomputable section

namespace BlowupDensity.Contracts.V3.Continuation

open Set
open NavierStokes.ProblemStatement (Space)
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V2.LocalTheory
open BlowupDensity.Contracts.V2.Continuation
open scoped ENNReal

/-- The whole-space H¹-uniform additions to the registered continuation API. -/
structure ContinuationV3API : Prop where
  /-- `appendix-a-local-theory.tex:146-151` at the H¹ ball: one `δ` is chosen
  before the restart time and datum, for one fixed force in the manuscript
  class. -/
  restartH1 :
    ∀ (ν : ℝ), 0 < ν →
      ∀ (f : SpaceTimeField), MemForceR f →
        ∀ (S : ℝ), 0 ≤ S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
          ∃ δ : ℝ, 0 < δ ∧
            ∀ t₀ ∈ Icc (0 : ℝ) S,
              ∀ (a' : SpatialField), a' ∈ initialClassR →
                sobolevENorm 1 a' ≤ K →
                  ∃ w : ClassicalSolutionR ν a' (timeShift t₀ f) δ,
                    ManuscriptLocalRegularity ν a' (timeShift t₀ f) δ w

  /-- `appendix-a-local-theory.tex:146-151` at the H¹ ball: the same
  fixed-force uniform restart gives a strict maximal-lifespan extension past
  the endpoint. -/
  restartBeyondH1 :
    ∀ (ν : ℝ), 0 < ν → ∀ (f : SpaceTimeField), MemForceR f →
      ∀ (S : ℝ), 0 < S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ (a : SpatialField) (u : SpaceTimeField) (p : SpaceTimeScalar),
            a ∈ initialClassR → SolvesBelow ν a f S u p →
              (∀ t ∈ Ico (0 : ℝ) S,
                sobolevENorm 1 (fun x : Space => u (t, x)) ≤ K) →
                  ENNReal.ofReal (S + δ) < maximalLifespanR ν a f

end BlowupDensity.Contracts.V3.Continuation
