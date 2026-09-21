import NSFormalization.Section3.T19.Projection

namespace NSFormalization.Section3.T19.Review466

open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10
open scoped ENNReal

/-- Deliberately false-to-the-proof mutation: widen the subcritical range. -/
example :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ s : ℝ, s < 3 / 4 →
        ∀ a : SpatialField, a ∈ initialClassT →
          ∀ g : SpaceTimeField, g ∈ forceClassT →
            ∀ r : ℝ≥0∞, 0 < r →
              ∃ f : SpaceTimeField,
                (a, f) ∈ extendedBreakdownSetT ν T ∧
                  forceSobolevENormT 1 s (fun z => f z - g z) < r := by
  intro ν hν T hT s hs a ha g hg r hr
  obtain ⟨f, hf, hdist⟩ :=
    fixedInitialDensity a ha ν hν T hT s hs g hg r hr
  exact ⟨f, ⟨ha, hf.1, hf.2⟩, hdist⟩

end NSFormalization.Section3.T19.Review466
