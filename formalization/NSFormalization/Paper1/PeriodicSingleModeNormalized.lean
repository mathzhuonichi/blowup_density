import NSFormalization.Paper1.PeriodicSingleModeLocal
import NSFormalization.Paper1.PeriodicPressureNormalization
import NSFormalization.Paper1.PeriodicLocalLifespan

/-! A small, unconditional bridge from the explicit shear mode to the
normalized pressure interface.  This is a concrete regression target for the
periodic pressure adapter; it does not assert the general local theory. -/
noncomputable section
namespace NSFormalization.Paper1.PeriodicSingleModeNormalized

open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Paper1.PeriodicSingleModeLocal
open NSFormalization.Paper1.PeriodicLifespan
open NSFormalization.Paper1.PeriodicPressureNormalization
open NSFormalization.Paper1.PeriodicLocalLifespan

theorem singleModeHeatFlow_normalized (ν A : ℝ) :
    ∃ U : Flow ν
      (fun x => (A * Real.sin ((2 * Real.pi) * x 1)) • coordinateVector 0)
      (0 : VelocityField) 1,
      IsNormalized U := by
  obtain ⟨U⟩ := singleModeHeatFlow ν A
  exact ⟨normalizedFlow U, normalizedFlow_isNormalized U⟩

end NSFormalization.Paper1.PeriodicSingleModeNormalized
