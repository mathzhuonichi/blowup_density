import Bindings.CompletedSobolevDensity

noncomputable section

namespace BlowupDensity.R46.Reviewer

open Set MeasureTheory
open Contracts.V1 Contracts.V1.Data
open NSFormalization.Paper3 (RealVectorSobolev)
open scoped ENNReal

/-- Fixed-radius specialization: the claimed dense breakdown set is inhabited. -/
example :
    ∃ f ∈ breakdownSetIn forceClassCompact 1 (0 : SpatialField) 1,
      ∃ D : ℝ → RealVectorSobolev 0,
        IsSobolevPath 0 f D ∧
          AEStronglyMeasurable D forceTimeMeasure ∧
            bochnerDatumENorm 1 0
              (D - (fun _ : ℝ => (0 : RealVectorSobolev 0))) < 1 := by
  have hdense := Bindings.completedSobolevDensity (0 : SpatialField)
    NSFormalization.Section4.A04.zero_mem_initialClassR
    1 (by norm_num) 1 (by norm_num) 1 (Or.inl rfl) 0
    (by norm_num [criticalOrder])
  exact hdense (fun _ : ℝ => (0 : RealVectorSobolev 0))
    (by
      change MemLp (0 : ℝ → RealVectorSobolev 0) 1 forceTimeMeasure
      exact MemLp.zero)
    1 (by norm_num)

end BlowupDensity.R46.Reviewer
