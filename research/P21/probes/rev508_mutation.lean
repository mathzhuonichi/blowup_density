import NSFormalization.Section3.T11.H1Restart

noncomputable section

open Set NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10 NSFormalization.Section3.T11
open scoped ENNReal

-- Substantive mutation: widen the datum ball from H¹ to L² by changing
-- the Sobolev-order constant from 1 to 0.  The H¹ theorem must not prove it.
/-- error: Type mismatch
  h1RestartT
has type
  ∀ (ν : ℝ),
    0 < ν →
      ∀ f ∈ forceClassT,
        ∀ (S : ℝ),
          0 ≤ S →
            ∀ (K : ℝ≥0∞),
              K ≠ ∞ →
                ∃ δ,
                  0 < δ ∧
                    ∀ t₀ ∈ Icc 0 S,
                      ∀ a' ∈ initialClassT,
                        periodicSobolevENorm 1 a' ≤ K → ∃ w, PeriodicLocalRegularity ν a' (timeShiftT t₀ f) δ w
but is expected to have type
  ∀ (ν : ℝ),
    0 < ν →
      ∀ f ∈ forceClassT,
        ∀ (S : ℝ),
          0 ≤ S →
            ∀ (K : ℝ≥0∞),
              K ≠ ∞ →
                ∃ δ,
                  0 < δ ∧
                    ∀ t₀ ∈ Icc 0 S,
                      ∀ a' ∈ initialClassT,
                        periodicSobolevENorm 0 a' ≤ K → ∃ w, PeriodicLocalRegularity ν a' (timeShiftT t₀ f) δ w -/
#guard_msgs in
example :
    ∀ (ν : ℝ), 0 < ν → ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 ≤ S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧ ∀ t₀ ∈ Icc (0 : ℝ) S,
          ∀ (a' : SpatialField), a' ∈ initialClassT → periodicSobolevENorm 0 a' ≤ K →
            ∃ w : ClassicalSolutionT ν a' (timeShiftT t₀ f) δ,
              PeriodicLocalRegularity ν a' (timeShiftT t₀ f) δ w := by
  exact h1RestartT
