/-
  Axiom + Contracts.V1 conformance probe for lane 117 (D01 / P2 = SL8 assembly),
  module `formalization/NSFormalization/Section4/D01/PressureJets.lean`.

  Check with:  cd verification && lake env lean ../research/D01/axioms_sl8_assembly.lean
  Expect: every `#print axioms` prints exactly [propext, Classical.choice, Quot.sound],
  and the `example` (final P2 theorem in Contracts.V1 vocabulary) elaborates silently.
-/
import NSFormalization.Section4.D01.PressureJets
import Contracts.V1.GradientL6

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.D01
open NSFormalization.Section4.A02 (ClassicalSolutionR)

/-- The final P2 theorem's conclusion in `Contracts.V1` vocabulary.  The local
`D01.SmoothSquareIntegrableJets` restatement is `rfl`-equal to
`BlowupDensity.Contracts.V1.SmoothSquareIntegrableJets` (`Bindings/DatumLemmas.lean:61-62`), so the
unconditional theorem discharges the contract-shaped goal directly (defeq). -/
example {ν : ℝ} {a : Space → Space} {f : VelocityField} {T : ℝ}
    (u : ClassicalSolutionR ν a f T) (hf : MemForceR f) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    BlowupDensity.Contracts.V1.SmoothSquareIntegrableJets
      (fun x : Space => pressureGradient u.pressure t x) :=
  pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR u hf ht

#print axioms orderZeroDatum_pressureGradient_eq
#print axioms isSobolevDatum_pressureGradient_lerayComplement
#print axioms pin_pressureGradient_datum
#print axioms pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR
#print axioms exists_isSobolevDatum_pressureGradient_slice
#print axioms temporalDerivative_slice_smoothSquareIntegrableJets_of_memForceR
