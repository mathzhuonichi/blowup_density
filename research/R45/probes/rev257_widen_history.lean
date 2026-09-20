import Bindings.RapidClassDensity

/-!
Reviewer negative probe.  This deliberately widens the history conclusion of
`regularReference_rapid` from `[0, τ]` to `[0, T]`.  Elaboration must fail at
the final `exact`, because the genuine theorem supplies only the former.
-/

noncomputable section

namespace BlowupDensity.Review257

open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Bindings
open scoped ENNReal

example (nu T : ℝ) (hnu : 0 < nu) (hT : 0 < T)
    (q : ℝ≥0∞) (hq : q = 1 ∨ q = 2) (s : ℝ)
    (hs : s < criticalOrder q.toReal)
    (a : SpatialField) (ha : a ∈ initialClassR)
    (g : SpaceTimeField) (hg : g ∈ forceClassRapid)
    (delta : ℝ) (hdelta : 0 < delta)
    (v : ClassicalSolutionR nu a g (T + delta))
    (tau : ℝ) (htau0 : 0 ≤ tau) (htauT : tau < T)
    (r eta : ℝ≥0∞) (hr : 0 < r) (heta : 0 < eta) :
    ∃ f : SpaceTimeField, f ∈ forceClassRapid ∧
      ∃ u : ClassicalSolutionR nu a f T,
        maximalLifespanR nu a f = ENNReal.ofReal T ∧
        forceSobolevENorm q s (f - g) < r ∧
        energyENorm T (u.velocity - v.velocity) < eta ∧
        (∀ t : ℝ, 0 ≤ t → t ≤ T →
          ∀ x : NavierStokes.ProblemStatement.Space,
            u.velocity (t, x) = v.velocity (t, x)) := by
  exact regularReference_rapid nu hnu T hT q hq s hs a ha g hg
    delta hdelta v tau htau0 htauT r eta hr heta

end BlowupDensity.Review257
