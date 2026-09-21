import Tests.MainThresholds

/-! Transitive audit and endpoint consumer checks for the four-field R41 V1. -/
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Bindings
open scoped ENNReal

#print axioms mainThresholds_forceClassR_eq
#print axioms mainThresholds_forceSobolevENorm_eq
#print axioms maximalPartial_maximalLifespanR_eq
#print axioms mainThresholds_breakdownSetR_eq
#print axioms mainThresholds_BreakdownDenseR_eq
#print axioms mainThresholds_nonDensity
#print axioms mainThresholds_energy_congr
#print axioms mainThresholds_energyConvergence
#print axioms mainThresholds
#print axioms BlowupDensity.Tests.checkedMainThresholds

/-- Equality is on the non-dense side of the L1 threshold. -/
example : ¬ RelativelyDense 1 (1 / 2) forceClassR (breakdownSetRZero 1 1) := by
  intro hd
  have h := (mainThresholds.zeroInitialDensityIff 1 (by norm_num)
    1 (by norm_num) 1 (Or.inl rfl) (1 / 2)).mp hd
  norm_num [criticalOrder] at h

/-- Equality is on the non-dense side of the L2 threshold. -/
example : ¬ RelativelyDense 2 (-1 / 2) forceClassR (breakdownSetRZero 1 1) := by
  intro hd
  have h := (mainThresholds.zeroInitialDensityIff 1 (by norm_num)
    1 (by norm_num) 2 (Or.inr rfl) (-1 / 2)).mp hd
  norm_num [criticalOrder] at h

/-- A concrete strictly subcritical order lies on the dense side. -/
example : RelativelyDense 2 (-1) forceClassR (breakdownSetRZero 1 1) :=
  (mainThresholds.zeroInitialDensityIff 1 (by norm_num) 1 (by norm_num)
    2 (Or.inr rfl) (-1)).mpr (by norm_num [criticalOrder])
