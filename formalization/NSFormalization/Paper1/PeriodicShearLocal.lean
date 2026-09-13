import NSFormalization.Paper1.PeriodicLifespan

/-!
# A linear heat/shear slice of the periodic local theory

The full arbitrary-data local-existence bridge is still open in Paper 1. This
file isolates a potentially non-constant slice for which the only analytic input
is the linear heat identity. A profile is required to be a smooth periodic
shear, with zero transverse transport and `∂ₜu = ν Δu`; the `Flow` witness
then follows by direct residual algebra.

The hypotheses are deliberately displayed instead of hidden behind an
existence axiom. Thus this module can be instantiated later by a proved
Fourier heat profile (for example a single transverse sine mode), while the
arbitrary periodic Navier--Stokes local theory remains a separate obligation.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicShearLocal

open Set
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Source
open NSFormalization.Paper1.PeriodicLifespan
open scoped ContDiff ENNReal

/-- A smooth periodic shear certificate. The fields `transport_free` and
`heat_balance` are the exact nonlinear and viscous identities needed by the
Navier--Stokes residual; they do not assert arbitrary-data local existence. -/
structure ShearHeatProfile (ν S : ℝ) where
  velocity : VelocityField
  pressure : PressureField
  horizon_pos : 0 < S
  velocity_smooth : ContDiffOn ℝ ∞ velocity (Ico (0 : ℝ) S ×ˢ univ)
  pressure_smooth : ContDiffOn ℝ ∞ pressure (Ico (0 : ℝ) S ×ˢ univ)
  velocity_periodic : UnitSpatialPeriodsOn (Ico (0 : ℝ) S) velocity
  pressure_periodic : UnitSpatialPeriodsOn (Ico (0 : ℝ) S) pressure
  initial_data : Space → Space
  initial : ∀ x, velocity (0, x) = initial_data x
  divergence_free : ∀ t ∈ Ico (0 : ℝ) S, ∀ x,
    spatialDivergence velocity t x = 0
  transport_free : ∀ t ∈ Ioo (0 : ℝ) S, ∀ x,
    advection velocity t x = 0
  heat_balance : ∀ t ∈ Ioo (0 : ℝ) S, ∀ x,
    temporalDerivative velocity t x = ν • spatialLaplacian velocity t x
  pressure_flat : ∀ t ∈ Ioo (0 : ℝ) S, ∀ x,
    pressureGradient pressure t x = 0

/-- The certificate gives an actual unforced periodic flow with its displayed
initial datum. The proof uses only the residual definition and the four
identities in `ShearHeatProfile`; no local-existence theorem is imported. -/
def ShearHeatProfile.flow (H : ShearHeatProfile ν S) :
    Flow ν H.initial_data (0 : VelocityField) S where
  velocity := H.velocity
  pressure := H.pressure
  horizon_pos := H.horizon_pos
  velocity_smooth := H.velocity_smooth
  pressure_smooth := H.pressure_smooth
  velocity_periodic := H.velocity_periodic
  pressure_periodic := H.pressure_periodic
  initial := H.initial
  divergence := H.divergence_free
  equation := by
    intro t ht x
    unfold NSFormalization.Source.residual
    rw [H.heat_balance t ht x, H.transport_free t ht x,
      H.pressure_flat t ht x]
    simp

theorem shearHeatProfile_nonempty (H : ShearHeatProfile ν S) :
    Nonempty (Flow ν H.initial_data (0 : VelocityField) S) :=
  ⟨H.flow⟩

theorem shearHeatProfile_lifespan_pos (H : ShearHeatProfile ν S) :
    0 < lifespan ν H.initial_data (0 : VelocityField) :=
  (ENNReal.ofReal_pos.mpr H.horizon_pos).trans_le (horizon_le_lifespan H.flow)

end NSFormalization.Paper1.PeriodicShearLocal
