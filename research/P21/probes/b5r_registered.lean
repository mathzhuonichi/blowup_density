import Tests.ContinuationV3
import NSFormalization.Section4.A04.ZeroSolution

/-!
# B5 R³ registered continuation probe

The checked V3 witness has only the standard logical axioms.  Its strict H¹
endpoint field is instantiated below on the genuine zero classical solution,
using one zero solution on every shorter horizon.
-/

#print axioms BlowupDensity.Tests.checkedContinuationV3
run_cmd BlowupDensity.TestSupport.checkAxioms ``BlowupDensity.Tests.checkedContinuationV3

noncomputable section

namespace BlowupDensity.Research.P21.B5RProbes

open Set
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V2.Continuation
open NSFormalization.Section4
open scoped ENNReal

/-- The registered zero fields solve the problem on every horizon below one. -/
private theorem zero_solvesBelow : SolvesBelow 1 0 0 1 0 0 := by
  intro b hb _hb1
  exact ⟨Bindings.maximalPartial_ofA02 (A04.zeroSol 1 b one_pos hb), rfl, rfl⟩

/-- Non-vacuity: V3's strict endpoint theorem applies to the zero solution with
`ν = S = 1` and H¹ radius zero. -/
example : ∃ δ : ℝ, 0 < δ ∧
    ENNReal.ofReal (1 + δ) < maximalLifespanR 1 0 0 := by
  obtain ⟨δ, hδ, hr⟩ := Tests.checkedContinuationV3.restartBeyondH1
    1 one_pos 0 A04.memForceR_zero 1 one_pos 0 (by simp)
  refine ⟨δ, hδ, hr 0 0 0 A04.zero_mem_initialClassR zero_solvesBelow ?_⟩
  intro t _ht
  change NSFormalization.Section4.D01.sobolevENorm 1 (0 : SpatialField) ≤ 0
  erw [NSFormalization.Section4.A03.sobolevENorm_eq
    (NSFormalization.Section4.D01.isSobolevDatum_zero 1)]
  simp

end BlowupDensity.Research.P21.B5RProbes
