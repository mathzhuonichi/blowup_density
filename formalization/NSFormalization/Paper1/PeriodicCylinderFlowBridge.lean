import Euler.SmoothCylinderFlow
import Euler.CylinderSmoothTimeField
import Euler.CylinderJetLp

/-!
# Cylinder flow bridge for Paper 1

The source library already constructs a genuine flow on the periodic cylinder
from a smooth deck-periodic cover velocity. This module exposes that result
in the Paper 1 namespace. It deliberately returns only the Lagrangian flow
map and its measure/inverse properties: no pressure or Navier--Stokes equation
is inferred from a velocity path alone.
-/

noncomputable section

namespace NSFormalization.Paper1.PeriodicCylinderFlowBridge

open Set MeasureTheory
open EulerLiftedGradientSpace EulerSmoothBanachFlow EulerSmoothCylinderFlow

variable (P T : ℝ) [Fact (0 < P)] (hT : 0 ≤ T)
  (A : SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent)
  (hA : ∀ (c : AddSubgroup.zmultiples P) (t : Icc (0 : ℝ) T) z,
    A.field t (z.1, (c : ℝ) + z.2) = A.field t z)
  (hdiv : ∀ t x,
    LinearMap.trace ℝ LiftTangent
      (fderiv ℝ (A.field t : LiftTangent → LiftTangent) x).toLinearMap = 0)

/-- The source flow maps descend to the periodic cylinder and preserve Haar
measure whenever the cover velocity is smooth, deck-periodic, and trace-free.
All hypotheses are explicit so this theorem cannot be confused with a PDE or
pressure-recovery statement. -/
theorem cylinder_flow_bridge (hA' : ∀ (c : AddSubgroup.zmultiples P) (t : Icc (0 : ℝ) T) z,
    A.field t (z.1, (c : ℝ) + z.2) = A.field t z)
    (hdiv' : ∀ t x,
      LinearMap.trace ℝ LiftTangent
        (fderiv ℝ (A.field t : LiftTangent → LiftTangent) x).toLinearMap = 0) :
    ∃ forward backward : ℝ → LiftDomain P → LiftDomain P,
      (∀ t, forward t = EulerSmoothCylinderFlow.forward P T hT A t) ∧
      (∀ t, backward t = EulerSmoothCylinderFlow.backward P T hT A t) ∧
      Continuous (Function.uncurry forward) ∧
      Continuous (Function.uncurry backward) ∧
      (∀ t, Function.LeftInverse (backward t) (forward t)) ∧
      (∀ t, Function.RightInverse (backward t) (forward t)) ∧
      (∀ t : Icc (0 : ℝ) T,
        MeasurePreserving (forward t) (liftMeasure P) (liftMeasure P)) ∧
      (∀ t : Icc (0 : ℝ) T,
        MeasurePreserving (backward t) (liftMeasure P) (liftMeasure P)) := by
  let fwd : ℝ → LiftDomain P → LiftDomain P :=
    EulerSmoothCylinderFlow.forward P T hT A
  let bwd : ℝ → LiftDomain P → LiftDomain P :=
    EulerSmoothCylinderFlow.backward P T hT A
  refine ⟨fwd, bwd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t; rfl
  · intro t; rfl
  · dsimp [fwd]
    exact EulerSmoothCylinderFlow.forward_joint_continuous P T hT A hA'
  · dsimp [bwd]
    exact EulerSmoothCylinderFlow.backward_joint_continuous P T hT A hA'
  · intro t
    exact EulerSmoothCylinderFlow.backward_forward P T hT A hA' t
  · intro t
    exact EulerSmoothCylinderFlow.forward_backward P T hT A hA' t
  · intro t
    exact EulerSmoothCylinderFlow.forward_measurePreserving P T hT A hA' hdiv' t
  · intro t
    exact EulerSmoothCylinderFlow.backward_measurePreserving P T hT A hA' hdiv' t

end NSFormalization.Paper1.PeriodicCylinderFlowBridge

namespace NSFormalization.Paper1.PeriodicCylinderFlowBridge
open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderSmoothTimeField
open EulerCylinderSmoothOrbit EulerLpCylinderTranslation
open scoped ContDiff BoundedContinuousFunction

variable (P T : ℝ) [Fact (0 < P)]
  {p : C(Icc (0 : ℝ) T, LiftL2 P)}
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))

lemma ofPath_deck_periodic (c : AddSubgroup.zmultiples P) (t : Icc (0 : ℝ) T)
    (z : LiftTangent) :
    (EulerCylinderSmoothTimeField.ofPath P p hp).field t (z.1, (c : ℝ) + z.2) =
      (EulerCylinderSmoothTimeField.ofPath P p hp).field t z := by
  rw [EulerCylinderSmoothTimeField.ofPath_apply, EulerCylinderSmoothTimeField.ofPath_apply]
  exact EulerCylinderJetLp.cover_periodic P
    (fun q => EulerCylinderSmoothOrbit.pointField P p hp t q) c z

end NSFormalization.Paper1.PeriodicCylinderFlowBridge

/- The source `ofPath` is a three-component field on the four-dimensional
   cover. It cannot be passed to `cylinder_flow_bridge`, which requires a
   `LiftTangent`-valued field. A future adapter must specify the fourth
   component and prove the resulting trace identity before applying the
   source flow theorem. No flow theorem for this missing lift is asserted. -/
