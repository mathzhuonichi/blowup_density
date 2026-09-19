import Bindings.Density

/-!
# T19 U15 non-vacuity probe

The registered headline density statement is instantiated at zero initial
datum and zero force with `ν = 1`, `T = 1`, and `s = 0`.  A specific force is
then selected from the resulting positive-radius existential conclusion.
-/

noncomputable section

namespace BlowupDensity.T19.AssemblyProbe

open Set
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Contracts.V1.TorusLocalTheory
open scoped ContDiff ENNReal

theorem zeroInitial_mem : (0 : SpatialField) ∈ initialClassT := by
  refine ⟨contDiff_const, ?_, ?_⟩
  · intro x i
    rfl
  · intro x
    simp [spatialDivergence, spatialDerivative]

theorem zeroForce_mem : (0 : SpaceTimeField) ∈ forceClassT := by
  refine ⟨contDiff_const, ?_, ∅, isCompact_empty, empty_subset _, ?_⟩
  · intro t _ht x i
    rfl
  · exact (show tsupport (0 : SpaceTimeField) ⊆
        (∅ : Set ℝ) ×ˢ (Set.univ : Set Space) by simp)

/-- The `∀`-shaped registered statement has a genuine force witness at the
fully explicit unit-viscosity, unit-horizon, order-zero parameters. -/
theorem zeroDensity_exists :
    ∃ f ∈ breakdownSetT 1 (0 : SpatialField) 1,
      forceSobolevENormT 1 0 (fun z => f z - (0 : SpaceTimeField) z) < 1 := by
  exact BlowupDensity.Bindings.Density.periodicDensityStatement_holds
    (0 : SpatialField) zeroInitial_mem
    (1 : ℝ) (by norm_num) (1 : ℝ) (by norm_num)
    (0 : ℝ) (by norm_num)
    (0 : SpaceTimeField) zeroForce_mem (1 : ℝ≥0∞) (by norm_num)

/-- A concrete selected force supplied by `prop:density` at the zero datum. -/
noncomputable def densityForce : SpaceTimeField :=
  Classical.choose zeroDensity_exists

theorem densityForce_breaksByOne :
    densityForce ∈ breakdownSetT 1 (0 : SpatialField) 1 :=
  (Classical.choose_spec zeroDensity_exists).1

theorem densityForce_closeToZero :
    forceSobolevENormT 1 0
        (fun z => densityForce z - (0 : SpaceTimeField) z) < 1 :=
  (Classical.choose_spec zeroDensity_exists).2

#print axioms zeroInitial_mem
#print axioms zeroForce_mem
#print axioms zeroDensity_exists
#print axioms densityForce
#print axioms densityForce_breaksByOne
#print axioms densityForce_closeToZero

end BlowupDensity.T19.AssemblyProbe
