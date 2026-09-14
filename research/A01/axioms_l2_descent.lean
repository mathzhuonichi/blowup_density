import NSFormalization.Section4.A01.L2Descent

/-! Conformance for lane 153 (`Section4/A01/L2Descent.lean`).  Every declaration prints exactly the
standard three axioms `[propext, Classical.choice, Quot.sound]`; non-vacuity witnesses show the
descent is inhabited (on `g = 0`) and genuinely inverts `ordinaryLift` on angle-invariant inputs. -/

open MeasureTheory
open NSFormalization.Section4.A01
open EulerMeanOrdinaryLift EulerLiftedGradientSpace

#print axioms exists_ordinaryLift_of_invariant
#print axioms word_descent_ae_top
#print axioms word_descent_ae_full
#print axioms hword_jet_full

-- Non-vacuity 1: the descent is inhabited on `g = 0`.
example : ∃ G : EulerMeanSolenoidal.L2, ordinaryLift G = (0 : LiftL2 1) :=
  exists_ordinaryLift_of_invariant 0 (fun θ => by simp)

-- Non-vacuity 2: on any `ordinaryLift G₀` (angle-invariant, possibly nonzero) the descent returns a
-- genuine preimage, so the statement is not vacuously about `0`.
example (G₀ : EulerMeanSolenoidal.L2) :
    ∃ G : EulerMeanSolenoidal.L2, ordinaryLift G = ordinaryLift G₀ := by
  refine exists_ordinaryLift_of_invariant (ordinaryLift G₀) (fun θ => ?_)
  rw [ordinaryLift_translation]
  congr 1
  simp

#print axioms exists_ordinaryLift_of_invariant
