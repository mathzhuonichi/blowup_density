import NSFormalization.Section4.A01.DatumPathContinuity

/-!
Axiom audit for lane 124 (row C1b-c8-0), module
`NSFormalization.Section4.A01.DatumPathContinuity`.  Every new declaration must
depend only on `[propext, Classical.choice, Quot.sound]`.  Plus two
instantiations of `continuous_orderZeroDatum` (step 2) to show non-vacuity:
a constant path and a nontrivial (identity) continuous path.
-/

open MeasureTheory
open NSFormalization.Section4.A01
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Section4.D01 (orderZeroDatum)

#print axioms componentCLM
#print axioms componentLp_eq_compLpL
#print axioms orderZeroDatumCLM
#print axioms orderZeroDatum_memLp_eq
#print axioms continuous_orderZeroDatum
#print axioms datumPath
#print axioms continuousOn_datumPath
#print axioms datumPath_isSobolevDatum

-- Non-vacuity: step 2 on a constant path (X = ℝ, U ≡ c).
example (c : EulerMeanSolenoidal.L2) :
    Continuous (fun _ : ℝ => orderZeroDatum (Lp.memLp c)) :=
  continuous_orderZeroDatum (fun _ : ℝ => c) continuous_const

-- Non-vacuity: step 2 on a nontrivial continuous path (the identity path).
example :
    Continuous (fun u : EulerMeanSolenoidal.L2 => orderZeroDatum (Lp.memLp u)) :=
  continuous_orderZeroDatum id continuous_id
