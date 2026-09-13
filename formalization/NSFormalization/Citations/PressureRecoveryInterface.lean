import Mathlib
/-! Domain-specific pressure recovery contracts. Status: OPEN/sorry. -/
namespace NSFormalization.Citations
structure PeriodicVelocity where field : Type
structure PeriodicForce where field : Type
structure PeriodicMeanZeroPressure where field : Type
  poisson : Prop
  mean_zero : Prop
axiom periodic_pressure_recovery (u : PeriodicVelocity) (f : PeriodicForce) :
  ∃! p : PeriodicMeanZeroPressure, p.poisson ∧ p.mean_zero
structure WholeSpaceVelocity where field : Type
structure WholeSpaceForce where field : Type
structure WholeSpaceGradientField where field : Type
structure ScalarPotential where field : Type
  modulo_time_function : Prop
axiom whole_space_pressure_gradient_recovery (u : WholeSpaceVelocity) (f : WholeSpaceForce) :
  ∃ G : WholeSpaceGradientField, ∃ p : ScalarPotential, p.modulo_time_function
end NSFormalization.Citations
