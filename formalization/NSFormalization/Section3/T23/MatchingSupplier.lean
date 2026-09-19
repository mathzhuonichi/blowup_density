import NSFormalization.Section3.T23.Boundary

/-! Local transport for the registered whole-space correction supplier. -/
noncomputable section
namespace NSFormalization.Section3.T23

open Set Filter Metric MeasureTheory
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Paper1.CorrectionProfile
open NSFormalization.Paper1.RadialPotential (timePotential)
open NSFormalization.Source.PhysicalRemoval (temporal_cutoff_support)
open scoped ContDiff Topology

/-- The formula fields identify the supplied correction, without choosing it again. -/
theorem WholeSpaceCorrectionAPI.correction_eq_physical {ν : ℝ} {u : VelocityField}
    {K : Set Space} (C : WholeSpaceCorrectionAPI ν u K) (ε : ℝ) :
    C.correction ε = physicalCorrection C.v C.x₀ C.T C.θ C.η ε := by
  have hp : C.potential = timePotential C.v C.x₀ := by
    funext z
    exact C.potential_formula z.1 z.2
  funext z
  rw [C.correction_formula ε z, hp]
  rfl

end NSFormalization.Section3.T23
