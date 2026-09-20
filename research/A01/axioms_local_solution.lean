import NSFormalization.Section4.A01.LocalSolution
import NSFormalization.Section4.A04.ZeroSolution
import Bindings.MaximalPartial

noncomputable section

open NSFormalization.Section4
open NSFormalization.Section4.A01

#print axioms transport_initial
#print axioms smoothL2_of_initialClassR
#print axioms solution_of_base
#print axioms exists_localSolution_smooth
#print axioms exists_localSolution
#print axioms localHorizon
#print axioms localHorizon_spec
#print axioms localHorizon_pos
#print axioms localSolution

-- Actual admissible input, with a positive chosen horizon and the specified datum.
example : Nonempty (A02.ClassicalSolutionR 1 0 0 (localHorizon 1 0 0)) := by
  exact ⟨localSolution 1 0 0 (by norm_num) A04.zero_mem_initialClassR A04.memForceR_zero⟩

-- Exact canonical contract solution-field type, via the existing structure bridge.
example : ∀ (ν : ℝ) (a : BlowupDensity.Contracts.V1.Data.SpatialField)
    (f : BlowupDensity.Contracts.V1.Data.SpaceTimeField),
    0 < ν → a ∈ BlowupDensity.Contracts.V1.Data.initialClassR →
    BlowupDensity.Contracts.V1.Data.MemForceR f →
    BlowupDensity.Contracts.V1.Data.ClassicalSolutionR ν a f (localHorizon ν a f) :=
  fun ν a f hν ha hf => BlowupDensity.Bindings.maximalPartial_ofA02
    (localSolution ν a f hν ha hf)

-- Reindexing preserves both physical fields definitionally.
example {ν S : ℝ} {a b : A02.SpatialField} {f : A02.SpaceTimeField}
    (w : A02.ClassicalSolutionR ν a f S) (h : a = b) :
    (transport_initial w h).velocity = w.velocity ∧
      (transport_initial w h).pressure = w.pressure := ⟨rfl, rfl⟩

example : localHorizon 0 0 0 = 1 := by simp [localHorizon]
