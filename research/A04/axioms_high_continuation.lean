import NSFormalization.Section4.A04.HighContinuation

/-!
Axiom audit + spec-conformance for A04 unit **G2** (lane 135),
`formalization/NSFormalization/Section4/A04/HighContinuation.lean`.

Every public declaration of the module must depend on exactly
`propext`, `Classical.choice`, `Quot.sound`.

The final `example` is the conformance check (mirrors
`research/A04/axioms_energy_identity_high.lean`): its type is the spec field
`regularizedNormDerivative` (`research/A04/Spec.lean:459-470`) written
token-for-token in the formalization vocabulary — the contract vocabulary
(`ClassicalSolutionR`, `initialClassR`, `MemForceR`, `sobolevNormAt`,
`HasSmoothSobolevPath`, `Cgron`) substituted by the local formalization
definitions the A04 modules use — and it is discharged by
`A04.regularizedNormDerivative`.  Elaboration succeeding is proof that the module
theorem has exactly the spec field's shape (with `Cgron m ν := (Chigh m)²/(4ν)`).
-/

noncomputable section
open Set MeasureTheory
open NavierStokes.ProblemStatement

open NSFormalization.Section4.A04
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField ClassicalSolutionR initialClassR)
open NSFormalization.Section4.D01 (MemForceR)
open scoped RealInnerProductSpace

#print axioms Cgron_pos
#print axioms young_high_real
#print axioms young_absorption_high
#print axioms deriv_normSq_absorbed
#print axioms deriv_normSq_absorbed_deriv
#print axioms regularizedNormDerivative

/-- Conformance: the spec field `regularizedNormDerivative` (`Spec.lean:459-470`),
token-for-token in formalization vocabulary, is inhabited by
`A04.regularizedNormDerivative`. -/
example : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ),
    0 < ν → a ∈ initialClassR → MemForceR f →
      ∀ w : ClassicalSolutionR ν a f T, HasSmoothSobolevPath T w.velocity →
        ∀ m : ℕ, 3 ≤ m → ∀ t ∈ Ioo (0 : ℝ) T, ∀ ζ : ℝ, 0 < ζ →
          ∃ d : ℝ,
            HasDerivAt
                (fun r : ℝ =>
                  Real.sqrt (sobolevNormAt (m : ℝ) w.velocity r ^ 2 + ζ ^ 2)) d t ∧
              d ≤ Cgron m ν * sobolevNormAt 2 w.velocity t ^ 2 *
                    Real.sqrt (sobolevNormAt (m : ℝ) w.velocity t ^ 2 + ζ ^ 2) +
                  sobolevNormAt (m : ℝ) f t :=
  regularizedNormDerivative
