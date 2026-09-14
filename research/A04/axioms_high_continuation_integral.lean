import NSFormalization.Section4.A04.HighContinuationIntegral

/-!
Axiom audit + spec-conformance for A04 unit **G2b** (lane 138),
`formalization/NSFormalization/Section4/A04/HighContinuationIntegral.lean`.

Checked with:
  cd verification && lake env lean ../research/A04/axioms_high_continuation_integral.lean

Every public declaration of the module must depend on exactly
`propext`, `Classical.choice`, `Quot.sound`.

The final `example` is the conformance check (mirrors
`research/A04/axioms_high_continuation.lean`): its type is the spec field
`highContinuationIntegral` (`research/A04/Spec.lean:471-494`) written
token-for-token in the formalization vocabulary — the contract vocabulary
(`ClassicalSolutionR`, `initialClassR`, `MemForceR`, `MemL1Hm`, `sobolevNormAt`,
`HasSmoothSobolevPath`, `Cgron`) substituted by the local formalization
definitions the A04 modules use — and it is discharged by
`A04.highContinuationIntegral`.  Elaboration succeeding is proof that the module
theorem has exactly the spec field's shape (with `Cgron m ν := (Chigh m)²/(4ν)`).
-/

noncomputable section
open Set MeasureTheory
open NSFormalization.Section4.A04
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField ClassicalSolutionR initialClassR)
open NSFormalization.Section4.D01 (MemForceR)

#print axioms highContinuationIntegral

/-- Conformance: the spec field `highContinuationIntegral` (`Spec.lean:471-494`),
token-for-token in formalization vocabulary, is inhabited by
`A04.highContinuationIntegral`. -/
example : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ),
    0 < ν → a ∈ initialClassR → MemForceR f → MemL1Hm f →
      ∀ w : ClassicalSolutionR ν a f T, HasSmoothSobolevPath T w.velocity →
        ∀ m : ℕ, 3 ≤ m → ∀ t₀ t : ℝ, 0 ≤ t₀ → t₀ ≤ t → t < T →
          IntervalIntegrable
              (fun s : ℝ =>
                Cgron m ν * sobolevNormAt 2 w.velocity s ^ 2 *
                    sobolevNormAt (m : ℝ) w.velocity s +
                  sobolevNormAt (m : ℝ) f s)
              volume t₀ t ∧
            sobolevNormAt (m : ℝ) w.velocity t ≤
              sobolevNormAt (m : ℝ) w.velocity t₀ +
                ∫ s in t₀..t,
                  (Cgron m ν * sobolevNormAt 2 w.velocity s ^ 2 *
                      sobolevNormAt (m : ℝ) w.velocity s +
                    sobolevNormAt (m : ℝ) f s) :=
  highContinuationIntegral
