import NSFormalization.Section3.T18.ForceAmplitude
import NSFormalization.Section3.T19.Threading

/-! Remark 3.13 for the fixed-ball inserted family constructed from raw data. -/
noncomputable section
namespace NSFormalization.Section3.T19
open Set Filter Topology
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open scoped ENNReal

/-- The concrete T19 family has unbounded force amplitudes as the scale vanishes. -/
theorem forceAmplitude_diverges {ν T δ : ℝ} (hν : 0 < ν)
    {a : SpatialField} {g : SpaceTimeField}
    (ha : a ∈ initialClassT) (hg : g ∈ forceClassT) (hT : 0 < T) (hδ : 0 < δ)
    (reference : ClassicalSolutionT ν a g (T + δ)) :
    Tendsto (fun ε : ℝ => ⨆ z,
      ‖(insertion hν ha hg hT hδ reference).force ε z - g z‖ₑ)
      (𝓝[>] (0 : ℝ)) (𝓝 ⊤) :=
  T18.forceAmplitude_diverges _ _

end NSFormalization.Section3.T19
