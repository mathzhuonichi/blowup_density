import NSFormalization.Section4.R41.NonDensityL1
import Bindings.MaximalPartial

open scoped ENNReal
namespace NonDensityConformance
open NSFormalization.Section4
open BlowupDensity.Contracts.V1

#print axioms NSFormalization.Section4.R41.angularOrderLowering_norm_le
#print axioms NSFormalization.Section4.R41.lowerVectorL_norm_le
#print axioms NSFormalization.Section4.R41.forceSobolevENorm_mono_order
#print axioms NSFormalization.Section4.R41.forceClassR
#print axioms NSFormalization.Section4.R41.breakdownSetIn
#print axioms NSFormalization.Section4.R41.breakdownSetR
#print axioms NSFormalization.Section4.R41.breakdownSetRZero
#print axioms NSFormalization.Section4.R41.RelativelyDense
#print axioms NSFormalization.Section4.R41.BreakdownDenseR
#print axioms NSFormalization.Section4.R41.criticalRadius_le_forceSobolevENorm
#print axioms NSFormalization.Section4.R41.nonDensityZero_L1
#print axioms NSFormalization.Section4.R41.zero_mem_forceClassR
#print axioms NSFormalization.Section4.R41.not_breakdownDenseR_zero_L1

example : R41.forceClassR = Data.forceClassR := rfl

theorem breakdownSetIn_eq : R41.breakdownSetIn = Data.breakdownSetIn := by
  funext Y ν a T
  unfold R41.breakdownSetIn Data.breakdownSetIn
  simp only [BlowupDensity.Bindings.maximalPartial_maximalLifespanR_eq]

 theorem breakdownSetR_eq : R41.breakdownSetR = Data.breakdownSetR := by
  funext ν a T
  exact congrFun (congrFun (congrFun (congrFun breakdownSetIn_eq R41.forceClassR) ν) a) T

 theorem breakdownSetRZero_eq : R41.breakdownSetRZero = Data.breakdownSetRZero := by
  funext ν T
  exact congrFun (congrFun (congrFun breakdownSetR_eq ν) (fun _ => 0)) T

example : R41.RelativelyDense = Data.RelativelyDense := rfl

 theorem BreakdownDenseR_eq : R41.BreakdownDenseR = Data.BreakdownDenseR := by
  funext ν a T q s
  unfold R41.BreakdownDenseR Data.BreakdownDenseR
  rw [breakdownSetR_eq]
  rfl

#print axioms breakdownSetIn_eq
#print axioms breakdownSetR_eq
#print axioms breakdownSetRZero_eq
#print axioms BreakdownDenseR_eq

 theorem nonDensityZero_L1 : ∀ ν T : ℝ, 0 < ν → 0 < T → ∀ s : ℝ, 1 / 2 ≤ s →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ f ∈ Data.breakdownSetRZero ν T,
      ENNReal.ofReal ρ ≤ Data.forceSobolevENorm 1 s f := by
  rw [← breakdownSetRZero_eq]
  exact R41.nonDensityZero_L1

 theorem not_breakdownDenseR_zero_L1 : ∀ ν T : ℝ, 0 < ν → 0 < T → ∀ s : ℝ,
    1 / 2 ≤ s → ¬ Data.BreakdownDenseR ν (fun _ => 0) T 1 s := by
  rw [← BreakdownDenseR_eq]
  exact R41.not_breakdownDenseR_zero_L1

#print axioms nonDensityZero_L1
#print axioms not_breakdownDenseR_zero_L1

example : (0 : Data.SpaceTimeField) ∈ Data.forceClassR := R41.zero_mem_forceClassR
example : ¬ Data.BreakdownDenseR 1 (fun _ => 0) 1 1 (1 / 2) :=
  not_breakdownDenseR_zero_L1 1 1 (by norm_num) (by norm_num) _ le_rfl
end NonDensityConformance
