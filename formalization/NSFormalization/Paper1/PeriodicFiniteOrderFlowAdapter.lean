import NSFormalization.Paper1.PeriodicCylinderFlowBridge
import NSFormalization.Paper1.PeriodicFiniteOrderPath

/-! Conditional adapter from finite-order data to the smooth cylinder-flow API. -/
noncomputable section
namespace NSFormalization.Paper1.PeriodicFiniteOrderFlowAdapter

open Set MeasureTheory
open EulerLiftedGradientSpace EulerSmoothBanachFlow EulerSmoothCylinderFlow

structure Adapter (P T : ℝ) [Fact (0 < P)] (hT : 0 ≤ T) where
  field : SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent
  deck_periodic : ∀ (c : AddSubgroup.zmultiples P) (t : Icc (0 : ℝ) T) z,
    field.field t (z.1, (c : ℝ) + z.2) = field.field t z
  trace_free : ∀ t x,
    LinearMap.trace ℝ LiftTangent
      (fderiv ℝ (field.field t : LiftTangent → LiftTangent) x).toLinearMap = 0

theorem flow (P T : ℝ) [Fact (0 < P)] (hT : 0 ≤ T)
    (B : Adapter P T hT) :
    ∃ forward backward : ℝ → LiftDomain P → LiftDomain P,
      (∀ t, forward t = EulerSmoothCylinderFlow.forward P T hT B.field t) ∧
      (∀ t, backward t = EulerSmoothCylinderFlow.backward P T hT B.field t) ∧
      Continuous (Function.uncurry forward) ∧
      Continuous (Function.uncurry backward) ∧
      (∀ t, Function.LeftInverse (backward t) (forward t)) ∧
      (∀ t, Function.RightInverse (backward t) (forward t)) ∧
      (∀ t : Icc (0 : ℝ) T, MeasurePreserving (forward t) (liftMeasure P) (liftMeasure P)) ∧
      (∀ t : Icc (0 : ℝ) T, MeasurePreserving (backward t) (liftMeasure P) (liftMeasure P)) := by
  exact NSFormalization.Paper1.PeriodicCylinderFlowBridge.cylinder_flow_bridge
    P T hT B.field B.deck_periodic B.trace_free

/-- Inverse identities for the concrete source flow maps supplied by an adapter.

This is deliberately conditional on `Adapter`: it exposes only the Lagrangian
inverse statements already proved by the smooth-cylinder library and makes no
claim about the finite-order mild path or the Navier--Stokes pressure. -/
theorem source_flow_inverses (P T : ℝ) [Fact (0 < P)] (hT : 0 ≤ T)
    (B : Adapter P T hT) (t : ℝ) :
    Function.LeftInverse
      (EulerSmoothCylinderFlow.backward P T hT B.field t)
      (EulerSmoothCylinderFlow.forward P T hT B.field t) ∧
    Function.RightInverse
      (EulerSmoothCylinderFlow.backward P T hT B.field t)
      (EulerSmoothCylinderFlow.forward P T hT B.field t) := by
  constructor
  · exact EulerSmoothCylinderFlow.backward_forward P T hT B.field
      B.deck_periodic t
  · exact EulerSmoothCylinderFlow.forward_backward P T hT B.field
      B.deck_periodic t

/-/ At each admissible time the descended source maps preserve the periodic
Haar measure in both directions.  This is a direct conditional consequence
of the smooth-cylinder theorem; in particular it does not assert that a
finite-order mild path supplies the required smooth field. -/
theorem source_flow_measure_preserving (P T : ℝ) [Fact (0 < P)] (hT : 0 ≤ T)
    (B : Adapter P T hT) (t : Icc (0 : ℝ) T) :
    MeasurePreserving
        (EulerSmoothCylinderFlow.forward P T hT B.field t)
        (liftMeasure P) (liftMeasure P) ∧
    MeasurePreserving
        (EulerSmoothCylinderFlow.backward P T hT B.field t)
        (liftMeasure P) (liftMeasure P) := by
  constructor
  · exact EulerSmoothCylinderFlow.forward_measurePreserving P T hT B.field
      B.deck_periodic B.trace_free t
  · exact EulerSmoothCylinderFlow.backward_measurePreserving P T hT B.field
      B.deck_periodic B.trace_free t

end NSFormalization.Paper1.PeriodicFiniteOrderFlowAdapter
