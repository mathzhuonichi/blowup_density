import Tests.ContinuationV2
noncomputable section
open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V2.Continuation
open scoped ENNReal

-- Substantive mutation: enlarge the datum class from an H7 ball to an H1 ball.
example :
    ∀ ν : ℝ, 0 < ν → ∀ f : SpaceTimeField, MemForceR f →
      ∀ S : ℝ, 0 ≤ S → ∀ K : ℝ≥0∞, K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ t₀ ∈ Icc (0 : ℝ) S, ∀ a' : SpatialField, a' ∈ initialClassR →
            sobolevENorm 1 a' ≤ K →
              δ ≤ NSFormalization.Section4.A01.localHorizon' ν a' (timeShift t₀ f) :=
  BlowupDensity.Tests.checkedContinuationV2.restart
