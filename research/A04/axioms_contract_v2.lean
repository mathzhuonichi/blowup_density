import Contracts.V2.EnergyHighPartial
import Bindings.EnergyHighPartialV2

/-!
Axiom audit + conformance for the A04 **version-2** contract
`A04.energy_high_partial_v2` (lane 141), registered in
`verification/contracts.json`.

Checked with:
  cd verification && lake env lean ../research/A04/axioms_contract_v2.lean

Every declaration in `Bindings/EnergyHighPartialV2.lean` — the version-two witness,
the four `rfl` facts (the `MemL1Hm` bridge, the `Cgron` value bonus, the
version-one-projection guard) — must depend on exactly `propext`,
`Classical.choice`, `Quot.sound`.  The acceptance test
`BlowupDensity.Tests.checkedEnergyHighPartialV2` is audited by
`verification/Tests/EnergyHighPartialV2.lean`'s `run_cmd TestSupport.checkAxioms`.

The conformance `example`s re-state the two new fields
(`regularizedNormDerivative`, `highContinuationIntegral`, `Spec.lean:459-494`)
token-for-token in the **contract** vocabulary and discharge them by the
version-two witness, so elaboration succeeding is proof that the contract has
exactly the spec-field shapes (with the opaque `Cgron`).
-/

noncomputable section

open Set MeasureTheory
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.EnergyHighPartial (sobolevNormAt HasSmoothSobolevPath)
open BlowupDensity.Contracts.V2.EnergyHighPartial (MemL1Hm)

#print axioms BlowupDensity.Bindings.energyHighPartialV2
#print axioms BlowupDensity.Bindings.energyHighPartialV2_memL1Hm_eq
#print axioms BlowupDensity.Bindings.energyHighPartialV2_Cgron_eq
#print axioms BlowupDensity.Bindings.energyHighPartial_of_v2

/-- Conformance: the version-two API is inhabited by the binding witness. -/
example : BlowupDensity.Contracts.V2.EnergyHighPartial.EnergyHighPartialV2API :=
  BlowupDensity.Bindings.energyHighPartialV2

/-- Conformance: `regularizedNormDerivative` (`Spec.lean:459-470`), token-for-token in
the contract vocabulary, is discharged by the version-two witness. -/
example :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ),
      0 < ν → a ∈ initialClassR → MemForceR f →
        ∀ w : ClassicalSolutionR ν a f T, HasSmoothSobolevPath T w.velocity →
          ∀ m : ℕ, 3 ≤ m → ∀ t ∈ Ioo (0 : ℝ) T, ∀ ζ : ℝ, 0 < ζ →
            ∃ d : ℝ,
              HasDerivAt
                  (fun r : ℝ =>
                    Real.sqrt (sobolevNormAt (m : ℝ) w.velocity r ^ 2 + ζ ^ 2)) d t ∧
                d ≤ BlowupDensity.Bindings.energyHighPartialV2.Cgron m ν *
                      sobolevNormAt 2 w.velocity t ^ 2 *
                      Real.sqrt (sobolevNormAt (m : ℝ) w.velocity t ^ 2 + ζ ^ 2) +
                    sobolevNormAt (m : ℝ) f t :=
  BlowupDensity.Bindings.energyHighPartialV2.regularizedNormDerivative

/-- Conformance: `highContinuationIntegral` (`Spec.lean:471-494`), token-for-token in
the contract vocabulary, is discharged by the version-two witness. -/
example :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ),
      0 < ν → a ∈ initialClassR → MemForceR f → MemL1Hm f →
        ∀ w : ClassicalSolutionR ν a f T, HasSmoothSobolevPath T w.velocity →
          ∀ m : ℕ, 3 ≤ m → ∀ t₀ t : ℝ, 0 ≤ t₀ → t₀ ≤ t → t < T →
            IntervalIntegrable
                (fun s : ℝ =>
                  BlowupDensity.Bindings.energyHighPartialV2.Cgron m ν *
                      sobolevNormAt 2 w.velocity s ^ 2 *
                      sobolevNormAt (m : ℝ) w.velocity s +
                    sobolevNormAt (m : ℝ) f s)
                volume t₀ t ∧
              sobolevNormAt (m : ℝ) w.velocity t ≤
                sobolevNormAt (m : ℝ) w.velocity t₀ +
                  ∫ s in t₀..t,
                    (BlowupDensity.Bindings.energyHighPartialV2.Cgron m ν *
                        sobolevNormAt 2 w.velocity s ^ 2 *
                        sobolevNormAt (m : ℝ) w.velocity s +
                      sobolevNormAt (m : ℝ) f s) :=
  BlowupDensity.Bindings.energyHighPartialV2.highContinuationIntegral

/-- Conformance: the fourth `rfl` bridge, contract `MemL1Hm` = implementation
`A04.MemL1Hm`. -/
example :
    BlowupDensity.Contracts.V2.EnergyHighPartial.MemL1Hm
      = NSFormalization.Section4.A04.MemL1Hm :=
  BlowupDensity.Bindings.energyHighPartialV2_memL1Hm_eq
