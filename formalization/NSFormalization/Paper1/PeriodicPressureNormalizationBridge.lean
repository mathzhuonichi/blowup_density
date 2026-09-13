import NSFormalization.Paper1.PeriodicPressureNormalization

/-!
# The normalized-flow certificate

`normalizedFlow` is defined by changing only the pressure representative of an
actual periodic flow.  This file exposes the resulting data in one theorem so
downstream arguments can consume the normalized representative without
reproving the projection facts field by field.  The time domains are kept
distinct: divergence and the mean-zero gauge hold on `Ico (0,S)`, while the
equation is required only on `Ioo (0,S)`.
-/
noncomputable section

namespace NSFormalization.Paper1.PeriodicPressureNormalization

open Set MeasureTheory
open NavierStokes NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration
open NSFormalization.Source

open NSFormalization.Paper1.PeriodicLifespan

/-/ Every actual flow has a normalized representative with all of the
manuscript-facing flow properties and the zero spatial pressure gauge. -/
theorem normalizedFlow_preserves_flow_properties
    {ν S : ℝ} {a : Space → Space} {f : VelocityField}
    (W : Flow ν a f S) :
    (∀ x, (normalizedFlow W).velocity (0, x) = a x) ∧
    (∀ t ∈ Ico (0 : ℝ) S, ∀ x,
      spatialDivergence (normalizedFlow W).velocity t x = 0) ∧
    UnitSpatialPeriodsOn (Ico (0 : ℝ) S) (normalizedFlow W).velocity ∧
    UnitSpatialPeriodsOn (Ico (0 : ℝ) S) (normalizedFlow W).pressure ∧
    (∀ t ∈ Ioo (0 : ℝ) S, ∀ x,
      Source.residual ν (normalizedFlow W).velocity
        (normalizedFlow W).pressure t x = f (t, x)) ∧
    (∀ t ∈ Ico (0 : ℝ) S,
      cubeIntegral (fun x : Space => (normalizedFlow W).pressure (t, x)) = 0) := by
  refine ⟨(normalizedFlow W).initial, (normalizedFlow W).divergence,
    (normalizedFlow W).velocity_periodic, (normalizedFlow W).pressure_periodic,
    (normalizedFlow W).equation, ?_⟩
  intro t ht
  exact normalizedFlow_mean_zero W ht

end NSFormalization.Paper1.PeriodicPressureNormalization
