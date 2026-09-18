import NSFormalization.Section3.T11.ExtendsBeyond

noncomputable section

namespace NSFormalization.Section3.T11.Rev337Negative

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open scoped ENNReal

/- A substantive mutation of U14: the extension horizon is changed from
   `S + δ` to `S - δ`.  The canonical theorem must not close this altered
   statement.  This file is intentionally expected to fail at `exact`. -/
def BadExtendsBeyondT (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (S : ℝ)
    (u : SpaceTimeField) (p : SpaceTimeScalar) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ v : ClassicalSolutionT ν a f (S - δ),
    (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
      v.velocity (t, x) = u (t, x)) ∧
    (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
      v.pressure (t, x) = p (t, x))

example (H : PeriodicQuantitativeLocalInput')
    (hHigh : ∀ (ν : ℝ), 0 < ν →
      ∀ (a : SpatialField), a ∈ initialClassT →
        ∀ (f : SpaceTimeField), f ∈ forceClassT →
          ∀ (S : ℝ), 0 < S →
            ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
              SolvesBelowT ν a f S u p → squaredHTwoIntegralT S u ≠ ⊤ →
                ∀ m : ℕ, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
                  ∀ t ∈ Ico (0 : ℝ) S,
                    periodicSobolevENorm (m : ℝ) (fun x ↦ u (t, x)) ≤ M) :
    ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (S : ℝ), 0 < S →
          ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
            SolvesBelowT ν a f S u p → squaredHTwoIntegralT S u ≠ ⊤ →
              BadExtendsBeyondT ν a f S u p := by
  exact extendsBeyond_of_input H hHigh

end NSFormalization.Section3.T11.Rev337Negative
