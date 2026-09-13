import NSFormalization.Section4.A01.PressureGauge

/-!
Axiom audit for A01 unit m4 (`Section4/A01/PressureGauge.lean`).
`lake env lean` this file from `verification/`; every public declaration must
report exactly `propext`, `Classical.choice`, `Quot.sound`.

The `example` below is typed token-identically to the contract spec field
`ManuscriptLocalRegularity.pressure_potential` (`research/A01/Spec.lean:227-229`),
with `u.pressure` in place of the structure's bound `pressure`, and is discharged
by `pressure_potential_of_classicalSolution`.
-/

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A01.RadialPotential
open NSFormalization.Section4.A01.PressureGauge
open NSFormalization.Section4.A02 (PressureGaugeEquivOn ClassicalSolutionR)

/-- Conformance: the m4 result inhabits the exact type of the spec field. -/
example {ν : ℝ} {a : Space → Space} {f : VelocityField} {T : ℝ}
    (u : ClassicalSolutionR ν a f T) :
    PressureGaugeEquivOn (Ico (0 : ℝ) T)
      (pressurePotential (fun z : SpaceTime => pressureGradient u.pressure z.1 z.2)) u.pressure :=
  pressure_potential_of_classicalSolution u

#print axioms pressureGradient_fderiv_slice
#print axioms fderiv_eq_of_pressureGradient_eq
#print axioms pressureGradient_apply
#print axioms contDiff_gradSlice
#print axioms hasSymmetricJacobian_pressureGradient
#print axioms pressure_potential_of_pointwise
#print axioms pressure_potential_of_classicalSolution
