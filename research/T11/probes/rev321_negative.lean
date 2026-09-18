import NSFormalization.Section3.T11.Restart

noncomputable section

namespace NSFormalization.Section3.T11.Rev321Negative

open Set
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open scoped ENNReal

/- A substantive mutation of the canonical restart field: H² datum control
   replaces the required H¹ control.  The exact restart proof must reject it. -/
example (H : PeriodicQuantitativeLocalInput') :
    ∀ (ν : ℝ), 0 < ν →
    ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 ≤ S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ t₀ ∈ Icc (0 : ℝ) S,
            ∀ (a' : SpatialField), a' ∈ initialClassT →
              periodicSobolevENorm 2 a' ≤ K →
                ∃ w : ClassicalSolutionT ν a' (timeShiftT t₀ f) δ,
                  PeriodicLocalRegularity ν a' (timeShiftT t₀ f) δ w := by
  exact restart H

end NSFormalization.Section3.T11.Rev321Negative
