import NSFormalization.Section4.D01.Pressure

/-!
Conformance check for D01 unit L9(c)-partial
(`formalization/NSFormalization/Section4/D01/Pressure.lean`).

Run with, from `verification/`:
  lake env lean ../research/D01/axioms_l9c.lean

Every result must depend only on the standard logical axioms
`propext`, `Classical.choice`, `Quot.sound`.
-/

open NSFormalization.Section4.D01
open NavierStokes.ProblemStatement (Space)

-- The algebraic identities from `momentum`.
#print axioms pressureGradient_slice_eq
#print axioms temporalDerivative_slice_eq

-- Velocity / nonlinear / viscous / force slices are H^∞ (discharged from the class).
#print axioms velocity_slice_smoothL2
#print axioms laplacian_slice_smoothL2
#print axioms advectionOf_smoothL2
#print axioms advection_slice_smoothL2
#print axioms forceSlice_smoothL2_of_memForceR

-- The conditional equivalence (the consumer's target, both directions), its two
-- packaging lemmas, and the forward corollary.
#print axioms pressureGradient_slice_smoothL2_of
#print axioms temporalDerivative_slice_smoothL2_of
#print axioms pressureGradient_slice_smoothL2_iff_temporalDerivative
#print axioms pressureGradient_slice_smoothSquareIntegrableJets

-- The target is literally the `Contracts.V1.SmoothSquareIntegrableJets` jet form
-- (restated as `SmoothSquareIntegrableJets`, defeq to `A05.SmoothL2`).
example (v : Space → Space) :
    SmoothSquareIntegrableJets v ↔ NSFormalization.Section4.A05.SmoothL2 v := Iff.rfl
