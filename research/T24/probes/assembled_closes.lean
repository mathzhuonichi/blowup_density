import NSFormalization.Section3.T24.MultipleAssembled

/-! Literal Ub4 field types from Multiple.lean, instantiated at RegionsData.
No complete MultipleRegionsAPI is assumed or claimed here: Ub5–Ub7 are separate. -/
noncomputable section
namespace NSFormalization.Section3.T24.AssembledProbe
open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T15
open NSFormalization.Section4.A02 (SpatialField)
variable {ν : ℝ} {u f : VelocityField} {p : PressureField}
  {K : Set Space} {M E : ℝ} (d : RegionsData ν u p f K M E)

theorem velocity_formula :
    d.assembledVelocity = finiteVelocitySum (fun j ↦ (d.component j).velocity) := by
  exact d.assembled_velocity_formula

theorem pressure_formula :
    d.assembledPressure = finitePressureSum (fun j ↦ (d.component j).pressure) := by
  exact d.assembled_pressure_formula

theorem force_formula : d.assembledForce =
    finiteForceSum (fun j ↦ periodizedScaledForce f (d.placement j).x₀ d.T (d.ε j)) := by
  exact d.assembled_force_formula

def solution : ClassicalSolutionT ν (0 : SpatialField) d.assembledForce d.T := by
  exact d.solution

theorem solution_pin :
    d.solution.velocity = d.assembledVelocity ∧ d.solution.pressure = d.assembledPressure := by
  exact d.solution_pin

theorem force_mem : d.assembledForce ∈ forceClassT := by
  exact d.force_mem

theorem rest : ∀ x : Space, d.assembledVelocity (0, x) = 0 := by
  exact d.rest

end NSFormalization.Section3.T24.AssembledProbe
