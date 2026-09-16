import NSFormalization.Section4.R43.ForcePath
open Set MeasureTheory
open NSFormalization.Section4.A02 (SpaceTimeField MemForceR)
open NSFormalization.Section4.R43

-- Mutation: add 1 to the FTC derivative; all hypotheses and proof steps retained.
theorem rev221_mutated_FTC {f : SpaceTimeField} (hf : MemForceR f)
    {S t : ℝ} (hS : 0 ≤ S) (ht : t ∈ Ioo (0 : ℝ) S) :
    HasDerivAt (criticalForcePrimitive f) (criticalForceAt f t + 1) t := by
  have hint : IntervalIntegrable (criticalForceAt f) volume 0 t :=
    criticalForceAt_intervalIntegrable hf ht.1.le
  have hcont : ContinuousAt (criticalForceAt f) t :=
    (criticalForceAt_continuousOn hf hS).continuousAt
      (Icc_mem_nhds ht.1 ht.2)
  exact intervalIntegral.integral_hasDerivAt_right hint
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
      ((criticalForceAt_continuousOn hf hS).mono Ioo_subset_Icc_self) t ht)
    hcont

