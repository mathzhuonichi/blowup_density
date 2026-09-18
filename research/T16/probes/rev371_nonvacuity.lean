import Tests.LocalPotential

noncomputable section
namespace BlowupDensity.Review371

open Set
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData

/- The registered binding applies to the genuinely nonzero constant reference
   `v = e₀`, with a nonempty chart cylinder and admissible scales. -/
example (x₀ : Space) :
    ∃ D : CutoffData,
      LocalPotentialAPI (fun _ => Contracts.V1.coordinateVector 0) (fun _ => 0)
        ({0} : Set Space) x₀ (1 / 4) 1 1 D := by
  apply Bindings.localPotential
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact isCompact_singleton
  · intro t _ x i; rfl
  · exact contDiffOn_const
  · intro t _ x _
    exact NSFormalization.Section3.T16.spatialDivergence_const_zero _ t x
  · intro t _
    rw [NSFormalization.Section3.T16.tsupport_zero_slice]
    exact empty_subset _

example : (Contracts.V1.coordinateVector 0 : Space) ≠ 0 := by
  intro h
  have hc := congrArg (fun z : Space => z 0) h
  simp [Contracts.V1.coordinateVector] at hc

end BlowupDensity.Review371
