import NSFormalization.Section3.T11.H1RestartBeyond

/-!
# B5 T³ endpoint probe

The canonical theorem inhabits the literal research target.  Its duration is
the unchanged `h1RestartT` duration used by the endpoint gluing proof.
-/

noncomputable section

namespace BlowupDensity.Research.P21.B5TEndpointProbe

open Set NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open scoped ENNReal

/-- Literal expansion of `Targets.lean:h1UniformEndpointT`. -/
example :
    ∀ (ν : ℝ), 0 < ν → ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 < S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ (a : SpatialField), a ∈ initialClassT →
            ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
              SolvesBelowT ν a f S u p →
                (∀ t ∈ Ico (0 : ℝ) S,
                  periodicSobolevENorm 1 (fun x ↦ u (t, x)) ≤ K) →
                    ∃ v : ClassicalSolutionT ν a f (S + δ),
                      (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
                        v.velocity (t, x) = u (t, x)) ∧
                      (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
                        v.pressure (t, x) = p (t, x)) :=
  NSFormalization.Section3.T11.restartBeyondH1T

end BlowupDensity.Research.P21.B5TEndpointProbe
