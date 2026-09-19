import NSFormalization.Section3.T23.MatchingSupplier
import NSFormalization.Paper1.CorrectionEnergy
import NSFormalization.Paper1.CorrectionVectorNorms

/-! Quantitative estimates for the same local correction family. -/
noncomputable section
namespace NSFormalization.Section3.T23

open Set MeasureTheory Filter
open NavierStokes NavierStokes.ProblemStatement
open scoped ENNReal

/-- Restricting space decreases both summands of the exact energy norm. -/
theorem domainEnergyENorm_le (Ω : Set Space) (T : ℝ) (w : VelocityField) :
    domainEnergyENorm Ω T w ≤ NSFormalization.Section3.T24.energyENorm T w := by
  apply add_le_add
  · exact essSup_mono_ae (Filter.Eventually.of_forall fun _ =>
      eLpNorm_mono_measure _ Measure.restrict_le_self)
  · apply ENNReal.rpow_le_rpow _ (by positivity)
    apply lintegral_mono
    intro t
    exact ENNReal.rpow_le_rpow (eLpNorm_mono_measure _ Measure.restrict_le_self) (by norm_num)

end NSFormalization.Section3.T23
