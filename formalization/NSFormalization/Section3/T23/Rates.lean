import NSFormalization.Section3.T23.NormBridge
import NSFormalization.Section3.T24.AffineEnergy
import NSFormalization.Paper1.ScalingLimits

/-! Domain restriction and closeness rates for T23. -/
noncomputable section
namespace NSFormalization.Section3.T23
open Set MeasureTheory Filter Topology
open NavierStokes.ProblemStatement
open NSFormalization.Section4.I02 (spatialGradient)
open scoped ENNReal Topology

/-- Restricting the spatial measure contracts both summands of the energy. -/
theorem domainEnergyENorm_le (Ω : Set Space) (T : ℝ) (z : VelocityField) :
    domainEnergyENorm Ω T z ≤ NSFormalization.Section3.T24.energyENorm T z := by
  apply add_le_add
  · exact essSup_mono_ae (Filter.Eventually.of_forall fun t =>
      eLpNorm_mono_measure (fun x => z (t, x)) Measure.restrict_le_self)
  · apply ENNReal.rpow_le_rpow _ (by norm_num)
    apply lintegral_mono
    intro t
    exact ENNReal.rpow_le_rpow
      (eLpNorm_mono_measure (fun x => spatialGradient z t x) Measure.restrict_le_self)
      (by norm_num)

end NSFormalization.Section3.T23
