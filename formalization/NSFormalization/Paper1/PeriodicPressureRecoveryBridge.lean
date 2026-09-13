import NSFormalization.Paper1.PeriodicLocalLifespan

/-!
# Pressure recovery and gauge bridge for Paper 1

This file isolates the pressure part of the periodic local-theory interface.
It does not assert existence of a pressure from a velocity equation.  Once a
smooth periodic pressure witness is supplied, the existing normalization
construction provides the canonical zero-mean gauge and preserves its spatial
gradient and residual.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicPressureRecoveryBridge

open Set
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Paper1.PeriodicLifespan
open NSFormalization.Paper1.PeriodicPressureNormalization
open NavierStokes.PeriodicIntegration

/-! The next lemma is the elementary pressure Poisson uniqueness bridge.  It is
deliberately stated for a single time slice: no pressure existence or Poisson
solvability is hidden in it.  Once two smooth periodic representatives have
the same gradient and the same cube mean, the gauge fixes their additive
constant. -/

/-- Canonical pressure gauge attached to a periodic flow witness. -/
def gaugePressure {ν S : ℝ} {a : Space → Space} {f : VelocityField}
    (W : Flow ν a f S) : PressureField := normalizedPressure W.pressure

/-- Gauge recovery preserves the pressure gradient on every physical slice. -/
theorem gaugePressure_gradient_eq {ν S : ℝ} {a : Space → Space} {f : VelocityField}
    (W : Flow ν a f S) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) S) (x : Space) :
    pressureGradient (gaugePressure W) t x = pressureGradient W.pressure t x := by
  exact normalizedPressure_gradient_eq W.pressure_smooth ht

/-- Gauge recovery preserves the Navier--Stokes residual pointwise. -/
theorem gaugePressure_residual_eq {ν : ℝ} {S : ℝ} {a : Space → Space}
    {f : VelocityField} (W : Flow ν a f S) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) S)
    (x : Space) :
    NSFormalization.Source.residual ν W.velocity (gaugePressure W) t x =
      NSFormalization.Source.residual ν W.velocity W.pressure t x := by
  exact normalizedPressure_residual_eq W.pressure_smooth ht

/-- The recovered gauge has zero spatial mean at every time in the slab. -/
theorem gaugePressure_zero_mean {ν S : ℝ} {a : Space → Space} {f : VelocityField}
    (W : Flow ν a f S) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) S) :
    cubeIntegral (fun x : Space => gaugePressure W (t, x)) = 0 := by
  exact pressureMean_zero_normalized_slice W.pressure_smooth ht

/-! The gauge is a projection: applying it to an already normalized flow does
not change the pressure on the physical slab.  This is the composition fact
used by overlap gluing; it is pointwise and therefore does not identify proof
fields of the surrounding `Flow` structure. -/
theorem gaugePressure_idempotent {ν S : ℝ} {a : Space → Space} {f : VelocityField}
    (W : Flow ν a f S) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) S) (x : Space) :
    gaugePressure (normalizedFlow W) (t, x) = gaugePressure W (t, x) := by
  exact normalizedPressure_idempotent W.pressure_smooth ht x

theorem normalizedFlow_pressure_eq_of_gauge_eq
    {ν S : ℝ} {a : Space → Space} {f : VelocityField}
    (U V : Flow ν a f S)
    (h : ∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
      gaugePressure U (t, x) = gaugePressure V (t, x)) :
    ∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
      (normalizedFlow U).pressure (t, x) = (normalizedFlow V).pressure (t, x) := by
  intro t ht x
  exact h t ht x

/-- The normalized flow satisfies the same forced equation pointwise. -/
theorem normalizedFlow_equation {ν S : ℝ} {a : Space → Space} {f : VelocityField}
    (W : Flow ν a f S) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) S) (x : Space) :
    NSFormalization.Source.residual ν (normalizedFlow W).velocity
        (normalizedFlow W).pressure t x = f (t, x) := by
  rw [show (normalizedFlow W).velocity = W.velocity from rfl,
    show (normalizedFlow W).pressure = gaugePressure W from rfl]
  rw [gaugePressure_residual_eq W ⟨ht.1.le, ht.2⟩ x]
  exact W.equation t ht x

end NSFormalization.Paper1.PeriodicPressureRecoveryBridge

namespace NSFormalization.Paper1.PeriodicPressureRecoveryBridge
open Set
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Paper1.PeriodicLifespan
open NSFormalization.Paper1.PeriodicPressureNormalization

/-- Pressure gauge is invariant under shortening a flow horizon: restriction
changes only the proof fields and leaves the pressure representative pointwise
unchanged.  This is the pressure part of restart compatibility. -/
theorem gaugePressure_restrict_eq
    {ν S R : ℝ} {a : Space → Space} {f : VelocityField}
    (W : Flow ν a f S) (hR : 0 < R) (hRS : R ≤ S)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) R) (x : Space) :
    gaugePressure (W.restrict hR hRS) (t, x) = gaugePressure W (t, x) := by
  rfl

/-- Consequently, normalizing before or after horizon restriction gives the
same pressure field on the restricted slab. -/
theorem normalizedFlow_restrict_pressure_eq
    {ν S R : ℝ} {a : Space → Space} {f : VelocityField}
    (W : Flow ν a f S) (hR : 0 < R) (hRS : R ≤ S)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) R) (x : Space) :
    (normalizedFlow (W.restrict hR hRS)).pressure (t, x) =
      (normalizedFlow W).pressure (t, x) := by
  exact gaugePressure_restrict_eq W hR hRS ht x

end NSFormalization.Paper1.PeriodicPressureRecoveryBridge

namespace NSFormalization.Paper1.PeriodicPressureRecoveryBridge
open Set
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Paper1.PeriodicLifespan
open NSFormalization.Paper1.PeriodicPressureNormalization

/-- The normalized restricted flow satisfies the same forced equation on its
shorter open time slab.  This is the PDE-semantic part of pressure restart
compatibility. -/
theorem normalizedFlow_restrict_equation
    {ν S R : ℝ} {a : Space → Space} {f : VelocityField}
    (W : Flow ν a f S) (hR : 0 < R) (hRS : R ≤ S)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) R) (x : Space) :
    NSFormalization.Source.residual ν
        (normalizedFlow (W.restrict hR hRS)).velocity
        (normalizedFlow (W.restrict hR hRS)).pressure t x = f (t, x) := by
  exact normalizedFlow_equation (W.restrict hR hRS) ht x

end NSFormalization.Paper1.PeriodicPressureRecoveryBridge
