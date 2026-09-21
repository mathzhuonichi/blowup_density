import NSFormalization.Section3.T11.H1RestartBeyond

/-!
# Reviewer negative probe for lane 511

This deliberately strengthens both overlap conclusions from `[0, S)` to
`[0, S]`.  The existing theorem must not inhabit this mutated statement: a
`SolvesBelowT` witness controls only strict sub-horizons, so its endpoint values
are unconstrained.
-/

noncomputable section

namespace BlowupDensity.Research.P21.Review511

open Set NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open scoped ENNReal

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
                      (∀ t ∈ Icc (0 : ℝ) S, ∀ x : Space,
                        v.velocity (t, x) = u (t, x)) ∧
                      (∀ t ∈ Icc (0 : ℝ) S, ∀ x : Space,
                        v.pressure (t, x) = p (t, x)) :=
  restartBeyondH1T

end BlowupDensity.Research.P21.Review511
