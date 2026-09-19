import NSFormalization.Section3.T19.Threading

noncomputable section

namespace Rev461Negative

open Set NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T18
open NSFormalization.Section3.T19
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open scoped ENNReal

variable {ν : ℝ} (hν : 0 < ν) {a : SpatialField} {g : SpaceTimeField}
  (ha : a ∈ initialClassT) (hg : g ∈ forceClassT) {T δ : ℝ}
  (hT : 0 < T) (hδ : 0 < δ) (reference : ClassicalSolutionT ν a g (T + δ))

local notation "ins" => insertion hν ha hg hT hδ reference

-- Deliberate mutation: the proved exact lifespan `T` is changed to `T + 1`.
example : ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀,
    maximalLifespanT ν a ((ins).force ε) = ENNReal.ofReal (T + 1) := by
  exact NSFormalization.Section3.T19.lifespan hν ha hg hT hδ reference

end Rev461Negative
