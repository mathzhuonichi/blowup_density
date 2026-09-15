import NSFormalization.Section4.A04.Continuation
import NSFormalization.Section4.A04.ZeroSolution
#print axioms NSFormalization.Section4.A04.lintegral_enorm_shift_le
#print axioms NSFormalization.Section4.A04.forceSobolevENormL1_timeShift_le
#print axioms NSFormalization.Section4.A04.lifespan_ge_of_solvesBelow
#print axioms NSFormalization.Section4.A04.restartBeyond_of_restartAt
#print axioms NSFormalization.Section4.A04.maximal_fields_of_solvesBelow
#print axioms NSFormalization.Section4.A04.restartBeyond
#print axioms NSFormalization.Section4.A04.lifespanInfiniteOfLocallyFinite_of_extendsBeyond
#print axioms NSFormalization.Section4.A04.extendsBeyond
#print axioms NSFormalization.Section4.A04.lifespanInfiniteOfLocallyFinite

open NSFormalization.Section4.A04 NSFormalization.Section4.A02
open scoped ENNReal

/-- Non-vacuity: the real zero solution supplies the whole shorter-horizon family. -/
example : SolvesBelow 1 0 0 1 0 0 := by
  intro b hb _hb1
  exact ⟨zeroSol 1 b one_pos hb, rfl, rfl⟩

/-- The supremum adapter consumes that concrete family. -/
example : ENNReal.ofReal 1 ≤ maximalLifespanR 1 0 0 := by
  apply lifespan_ge_of_solvesBelow (u := 0) (p := 0) one_pos
  intro b hb _hb1
  exact ⟨zeroSol 1 b one_pos hb, rfl, rfl⟩

/-- Zero translation is the identity as a total spacetime field. -/
example (f : SpaceTimeField) : timeShift 0 f = f := by
  funext z
  simp [timeShift]

/-- The force-tail estimate applies even without an ambient force-class hypothesis. -/
example (f : SpaceTimeField) :
    forceSobolevENormL1 1 (timeShift 0 f) ≤ forceSobolevENormL1 1 f :=
  forceSobolevENormL1_timeShift_le 1 f 0 le_rfl
