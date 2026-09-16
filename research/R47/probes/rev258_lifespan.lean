import Bindings.GridAssembly
open BlowupDensity.Contracts.V1.Data BlowupDensity.Research.R47.Draft
open Set
-- Mutate the exact maximal lifespan from T to T+1, retaining every argument.
example {ν T δ : ℝ} {a : SpatialField} {g : SpaceTimeField}
    {reference : ClassicalSolutionR ν a g (T + δ)} {n : ℕ} {grids : Fin n → Grid}
    (F : RGridFamily ν a g T δ reference n grids)
    (ε : ℝ) (hε : ε ∈ Ioc (0 : ℝ) F.ε₀) :
    maximalLifespanR ν a (F.force ε) = ENNReal.ofReal (T + 1) := by
  exact F.lifespan ε hε
