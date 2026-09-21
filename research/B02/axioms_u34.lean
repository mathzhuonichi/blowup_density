import Contracts.V1.Data
import NSFormalization.Section4.B02.LowFrequency

/-!
Conformance check for B02 units 3 and 4.

Each `example` is stated with the *exact* type of the corresponding field of
`research/B02/Spec.lean`'s `HomogeneousApproxAPI` (using the frozen definitions
`SpatialField`, `Space`, `angularFourier` of `Contracts.V1.Data`), and is
discharged by the theorem proved in
`NSFormalization.Section4.B02.LowFrequency`.  The `#print axioms` calls confirm
the transitive axiom set is exactly `propext`, `Classical.choice`, `Quot.sound`.
-/

open Set MeasureTheory NavierStokes.ProblemStatement NSFormalization.Source
open BlowupDensity.Contracts.V1.Data

-- Spec field `lowFrequencyIntegrable` (research/B02/Spec.lean:370)
example : ∀ s : ℝ, -3 / 2 < s →
    IntegrableOn (fun ξ : Space => ‖ξ‖ ^ (2 * s)) (Metric.ball (0 : Space) 1) volume :=
  NSFormalization.Section4.B02.lowFrequencyIntegrable

-- Spec field `lowFrequencyIntegral` (research/B02/Spec.lean:379)
example :
    (∫ ξ in Metric.ball (0 : Space) 1, ‖ξ‖ ^ (2 * (-1 : ℝ))) = 4 * Real.pi :=
  NSFormalization.Section4.B02.lowFrequencyIntegral

-- Spec field `fourierSupBound` (research/B02/Spec.lean:397)
example : ∀ k : SpatialField, MemLp k 1 volume →
    ∀ ξ : Space,
      Real.sqrt (∑ i : Fin 3, ‖angularFourier (fun x : Space => ((k x i : ℝ) : ℂ)) ξ‖ ^ 2) ≤
        (2 * Real.pi) ^ (-(3 : ℝ) / 2) * ∫ x : Space, ‖k x‖ :=
  NSFormalization.Section4.B02.fourierSupBound

#print axioms NSFormalization.Section4.B02.lowFrequencyIntegrable
#print axioms NSFormalization.Section4.B02.lowFrequencyIntegral
#print axioms NSFormalization.Section4.B02.fourierSupBound
