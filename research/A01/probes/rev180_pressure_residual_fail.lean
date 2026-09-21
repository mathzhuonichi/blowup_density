import NSFormalization.Section4.A01.ConstructorAssembly

noncomputable section
namespace Rev180PressureResidual

open Set
open NavierStokes.ProblemStatement (Space VelocityField)
open NSFormalization.Section4.A01
open scoped ContDiff

example {T ν : ℝ} (f velocity : VelocityField)
    (hc3 : ContDiffOn ℝ ∞ velocity (Ico (0 : ℝ) T ×ˢ (univ : Set Space))) :
    ContDiffOn ℝ ∞ (pressureOfVelocity ν f velocity)
      (Ico (0 : ℝ) T ×ˢ (univ : Set Space)) := by
  exact pressure_smooth_of_velocity_smooth ν f velocity hc3

end Rev180PressureResidual
