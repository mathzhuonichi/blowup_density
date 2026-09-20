import NSFormalization.Section3.T11.LocalTheory
import NSFormalization.Paper1.PeriodicLocalLifespan

/-!
# Fieldwise conversion between the two periodic flow structures

`ClassicalSolutionT` carries three regularity fields that the older Paper 1
`Flow` structure does not.  The remaining fields have definitionally equal
types, including the two differently named residual and periodicity
predicates.  This module records those spelling equalities, the fieldwise
conversions, and their round trips.
-/

noncomputable section

namespace NSFormalization.Section3.T11

open Set MeasureTheory
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T10
open NSFormalization.Paper1.PeriodicLifespan
open NSFormalization.Paper1.PeriodicLocalLifespan
open scoped ContDiff

/-! ## Definitional spelling bridges -/

/-- The T10 and Paper 1 residual spellings have identical bodies. -/
theorem source_residual_eq_navierStokesResidual (ν : ℝ) (u : SpaceTimeField)
    (p : SpaceTimeScalar) (t : ℝ) (x : Space) :
    Source.residual ν u p t x =
      NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x :=
  rfl

/-- The T10 and Paper 1 unit-periodicity predicates have identical bodies. -/
theorem isPeriodicOn_iff_unitSpatialPeriodsOn {E : Type*} (I : Set ℝ)
    (z : SpaceTime → E) :
    IsPeriodicOn I z ↔ UnitSpatialPeriodsOn I z :=
  Iff.rfl

/-! ## Structure conversions -/

/-- Forget the three extra T10 regularity fields of a classical periodic solution. -/
def toFlow {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) : Flow ν a f T where
  velocity := w.velocity
  pressure := w.pressure
  horizon_pos := w.horizon_pos
  velocity_smooth := w.velocity_smooth
  pressure_smooth := w.pressure_smooth
  velocity_periodic := w.velocity_periodic
  pressure_periodic := w.pressure_periodic
  initial := w.initial
  divergence := w.divergence
  equation := w.momentum

/-- Add the Sobolev, pressure-gradient, and pressure-gauge fields absent from
the older Paper 1 flow structure. -/
def ofFlow {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (U : Flow ν a f T)
    (hs : ∀ m : ℕ, ∃ G : ℝ → PeriodicSobolev (m : ℝ),
      ContinuousOn G (Ico (0 : ℝ) T) ∧
        ∀ t ∈ Ico (0 : ℝ) T,
          IsPeriodicDatum (m : ℝ) (fun x ↦ U.velocity (t, x)) (G t))
    (hg : ∀ t ∈ Ico (0 : ℝ) T,
      MemLp (torusLift (fun x ↦ pressureGradient U.pressure t x)) 2
        periodicTorusMeasure)
    (hn : PressureGaugeT (Ico (0 : ℝ) T) U.pressure) :
    ClassicalSolutionT ν a f T where
  velocity := U.velocity
  pressure := U.pressure
  horizon_pos := U.horizon_pos
  velocity_smooth := U.velocity_smooth
  pressure_smooth := U.pressure_smooth
  initial := U.initial
  divergence := U.divergence
  momentum := U.equation
  sobolev := hs
  pressure_gradient := hg
  velocity_periodic := U.velocity_periodic
  pressure_periodic := U.pressure_periodic
  pressure_gauge := hn

@[simp] theorem toFlow_velocity {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) :
    (toFlow w).velocity = w.velocity :=
  rfl

@[simp] theorem toFlow_pressure {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) :
    (toFlow w).pressure = w.pressure :=
  rfl

@[simp] theorem ofFlow_velocity {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (U : Flow ν a f T) (hs hg hn) :
    (ofFlow U hs hg hn).velocity = U.velocity :=
  rfl

@[simp] theorem ofFlow_pressure {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (U : Flow ν a f T) (hs hg hn) :
    (ofFlow U hs hg hn).pressure = U.pressure :=
  rfl

/-- Forgetting immediately after adding the three extra fields recovers the
original Paper 1 flow. -/
@[simp] theorem toFlow_ofFlow {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (U : Flow ν a f T) (hs hg hn) :
    toFlow (ofFlow U hs hg hn) = U := by
  rfl

/-- Adding back a T10 solution's own three extra fields after forgetting them
recovers the original solution. -/
@[simp] theorem ofFlow_toFlow {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) :
    ofFlow (toFlow w) w.sobolev w.pressure_gradient w.pressure_gauge = w := by
  rfl

/-! ## Force-class transport -/

/-- A globally smooth compact positive-time T10 force belongs to the weaker
Paper 1 local-theory force class. -/
theorem memForceT_to_isSmoothPeriodicForce {f : SpaceTimeField}
    (hf : MemForceT f) : IsSmoothPeriodicForce f :=
  ⟨fun _ _ ↦ hf.1.contDiffOn,
    fun t _ ↦ hf.2.1 t (mem_univ t)⟩

end NSFormalization.Section3.T11
