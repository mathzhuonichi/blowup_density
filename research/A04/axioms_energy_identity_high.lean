import NSFormalization.Section4.A04.EnergyIdentityHigh

/-!
Axiom audit + spec-conformance for the eq:Rhigh assembly lane (128),
`formalization/NSFormalization/Section4/A04/EnergyIdentityHigh.lean`.

Every public declaration of the module must depend on exactly
`propext`, `Classical.choice`, `Quot.sound`.

The final `example` is the conformance check (mirrors `research/A04/axioms_sl5c.lean`):
its type is the spec field `energyIdentityHigh` (`research/A04/Spec.lean:424-434`)
written token-for-token in the formalization vocabulary — the contract vocabulary
(`ClassicalSolutionR`, `initialClassR`, `MemForceR`, `sobolevNormAt`,
`gradientSobolevNormAt`, `HasSmoothSobolevPath`, `Chigh`) substituted by the local
formalization definitions the A04 modules use — and it is discharged by
`A04.energyIdentityHigh`.  Elaboration succeeding is proof that the module theorem
has exactly the spec field's shape (with `Chigh m := A03.outerTameConst m`).
-/

noncomputable section
open Set MeasureTheory
open NavierStokes.ProblemStatement

open NSFormalization.Section4.A04
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField ClassicalSolutionR initialClassR)
open NSFormalization.Section4.D01 (MemForceR)
open scoped RealInnerProductSpace

#print axioms Chigh_pos
#print axioms energyIdentityHigh_core
#print axioms energyIdentityHigh

/-- Conformance: the spec field `energyIdentityHigh` (`Spec.lean:424-434`),
token-for-token in formalization vocabulary, is inhabited by `A04.energyIdentityHigh`. -/
example : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ),
    0 < ν → a ∈ initialClassR → MemForceR f →
      ∀ w : ClassicalSolutionR ν a f T, HasSmoothSobolevPath T w.velocity →
        ∀ m : ℕ, 3 ≤ m → ∀ t ∈ Ioo (0 : ℝ) T,
          ∃ d : ℝ,
            HasDerivAt (fun r : ℝ => sobolevNormAt (m : ℝ) w.velocity r ^ 2) d t ∧
              (1 / 2) * d + ν * gradientSobolevNormAt (m : ℝ) w.velocity t ^ 2 ≤
                Chigh m * sobolevNormAt 2 w.velocity t *
                    sobolevNormAt (m : ℝ) w.velocity t *
                    gradientSobolevNormAt (m : ℝ) w.velocity t +
                  sobolevNormAt (m : ℝ) f t * sobolevNormAt (m : ℝ) w.velocity t :=
  energyIdentityHigh
