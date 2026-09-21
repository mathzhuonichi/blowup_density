import NSFormalization.Section3.T11.FlowConversion

/-!
# U1 fieldwise-conversion probe

Each U1 target is restated here against the canonical structures.  The final
example exhibits an actual member of the source force class, so the transport
statement is not merely implication-shaped.
-/

noncomputable section

namespace NSFormalization.Section3.T11.Probe

open Set MeasureTheory
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open NSFormalization.Paper1.PeriodicLifespan
open NSFormalization.Paper1.PeriodicLocalLifespan
open scoped ContDiff

example (ν : ℝ) (u : SpaceTimeField) (p : SpaceTimeScalar) (t : ℝ) (x : Space) :
    Source.residual ν u p t x =
      NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x :=
  source_residual_eq_navierStokesResidual ν u p t x

example {E : Type*} (I : Set ℝ) (z : SpaceTime → E) :
    IsPeriodicOn I z ↔ UnitSpatialPeriodsOn I z :=
  isPeriodicOn_iff_unitSpatialPeriodsOn I z

example {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) : Flow ν a f T :=
  toFlow w

example {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (U : Flow ν a f T)
    (hs : ∀ m : ℕ, ∃ G : ℝ → PeriodicSobolev (m : ℝ),
      ContinuousOn G (Ico (0 : ℝ) T) ∧
        ∀ t ∈ Ico (0 : ℝ) T,
          IsPeriodicDatum (m : ℝ) (fun x ↦ U.velocity (t, x)) (G t))
    (hg : ∀ t ∈ Ico (0 : ℝ) T,
      MemLp (torusLift (fun x ↦ pressureGradient U.pressure t x)) 2
        periodicTorusMeasure)
    (hn : PressureGaugeT (Ico (0 : ℝ) T) U.pressure) :
    ClassicalSolutionT ν a f T :=
  ofFlow U hs hg hn

example {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (U : Flow ν a f T) (hs hg hn) :
    toFlow (ofFlow U hs hg hn) = U :=
  toFlow_ofFlow U hs hg hn

example {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) :
    ofFlow (toFlow w) w.sobolev w.pressure_gradient w.pressure_gauge = w :=
  ofFlow_toFlow w

example {f : SpaceTimeField} :
    MemForceT f → IsSmoothPeriodicForce f :=
  memForceT_to_isSmoothPeriodicForce

/-- The zero force is a concrete member of `MemForceT`, hence the force-class
transport has an inhabited source. -/
example : IsSmoothPeriodicForce (0 : SpaceTimeField) := by
  apply memForceT_to_isSmoothPeriodicForce
  refine ⟨contDiff_const, ?_, ∅, isCompact_empty, empty_subset _, ?_⟩
  · intro t _ x i
    rfl
  · simp

end NSFormalization.Section3.T11.Probe
