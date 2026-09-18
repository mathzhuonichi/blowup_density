import NSFormalization.Section3.T11.Restart

/-! Exact target-shape and non-vacuity probe for T11/U10--U11. -/

noncomputable section

namespace NSFormalization.Section3.T11.RestartProbe

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open scoped ContDiff ENNReal

/-- The `PeriodicContinuationAPI.restart` field copied verbatim from
`api_on_canonical.lean`. -/
example (H : PeriodicQuantitativeLocalInput') :
    ∀ (ν : ℝ), 0 < ν →
    ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 ≤ S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ t₀ ∈ Icc (0 : ℝ) S,
            ∀ (a' : SpatialField), a' ∈ initialClassT →
              periodicSobolevENorm 1 a' ≤ K →
                ∃ w : ClassicalSolutionT ν a' (timeShiftT t₀ f) δ,
                  NSFormalization.Section3.T11.PeriodicLocalRegularity
                    ν a' (timeShiftT t₀ f) δ w := by
  exact restart H

/-- The selected `horizon` data field has the exact API type. -/
example (H : PeriodicQuantitativeLocalInput') :
    ℝ → SpatialField → SpaceTimeField → ℝ :=
  (periodicLocalTheoryAPI_of_input H).horizon

/-- The `PeriodicLocalTheoryAPI.solution` field copied verbatim. -/
example (H : PeriodicQuantitativeLocalInput') :
    ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ClassicalSolutionT ν a f
          ((periodicLocalTheoryAPI_of_input H).horizon ν a f) := by
  exact (periodicLocalTheoryAPI_of_input H).solution

/-- The `PeriodicLocalTheoryAPI.regularity` field copied verbatim. -/
example (H : PeriodicQuantitativeLocalInput') :
    ∀ (ν : ℝ) (hν : 0 < ν)
    (a : SpatialField) (ha : a ∈ initialClassT)
    (f : SpaceTimeField) (hf : f ∈ forceClassT),
      NSFormalization.Section3.T11.PeriodicLocalRegularity ν a f
        ((periodicLocalTheoryAPI_of_input H).horizon ν a f)
        ((periodicLocalTheoryAPI_of_input H).solution ν hν a ha f hf) := by
  exact (periodicLocalTheoryAPI_of_input H).regularity

/-- Non-vacuity for the one named input: the exact conclusion-side hypotheses
and regular solution are simultaneously inhabited with nonzero velocity and
nonzero force. -/
example :
    ∃ (K : ℝ≥0∞) (M : ℕ → ℝ≥0∞) (a : SpatialField) (g : SpaceTimeField),
      K ≠ ⊤ ∧ (∀ m, M m ≠ ⊤) ∧ a ∈ initialClassT ∧
      periodicSobolevENorm 1 a ≤ K ∧ ContDiff ℝ ∞ g ∧ IsPeriodicOn univ g ∧
      (∀ m : ℕ, forceSobolevENormT 1 (m : ℝ) g ≤ M m) ∧
      ∃ w : ClassicalSolutionT 1 a g 1,
        PeriodicLocalRegularity 1 a g 1 w ∧
        w.velocity (0, 0) ≠ 0 ∧ g (0, 0) ≠ 0 := by
  exact nonzero_forced_witness'

end NSFormalization.Section3.T11.RestartProbe
