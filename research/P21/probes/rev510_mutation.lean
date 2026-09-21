import Tests.ContinuationV3

/-!
# Intentional negative probe for lane 510

This substantively flips the strict endpoint inequality.  Applying the checked
theorem must fail because it proves `ofReal (S + δ) < maximalLifespanR`, not
the reversed relation below.
-/

noncomputable section

namespace BlowupDensity.Research.P21.Rev510

open Set
open NavierStokes.ProblemStatement (Space)
open Contracts.V1.Data
open Contracts.V2.Continuation
open scoped ENNReal

example :
    ∀ (ν : ℝ), 0 < ν → ∀ (f : SpaceTimeField), MemForceR f →
      ∀ (S : ℝ), 0 < S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ (a : SpatialField) (u : SpaceTimeField) (p : SpaceTimeScalar),
            a ∈ initialClassR → SolvesBelow ν a f S u p →
              (∀ t ∈ Ico (0 : ℝ) S,
                sobolevENorm 1 (fun x : Space => u (t, x)) ≤ K) →
                  maximalLifespanR ν a f < ENNReal.ofReal (S + δ) := by
  exact Tests.checkedContinuationV3.restartBeyondH1

end BlowupDensity.Research.P21.Rev510
