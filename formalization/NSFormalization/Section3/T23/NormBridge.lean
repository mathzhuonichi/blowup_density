import NSFormalization.Section3.T23.Boundary
import NSFormalization.Section4.D01.HalfOrder

/-! Slice-integral bounds for the canonical measurable-path Sobolev norm. -/
noncomputable section
namespace NSFormalization.Section3.T23
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.D01
open scoped ENNReal

/-- A measurable realizing path dominates the slice infima; taking its infimum
also covers the case where no path exists. -/
theorem lintegral_sobolevENorm_le_forceSobolevENorm (s : ℝ) (f : VelocityField) :
    (∫⁻ t in Ioi (0 : ℝ), sobolevENorm s (fun x => f (t, x))) ≤
      forceSobolevENorm 1 s f := by
  apply le_iInf
  rintro ⟨G, hG, _⟩
  change _ ≤ eLpNorm G 1 forceTimeMeasure
  rw [eLpNorm_one_eq_lintegral_enorm]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact iInf_le_of_le ⟨G t, hG t ht.le⟩ le_rfl

end NSFormalization.Section3.T23
