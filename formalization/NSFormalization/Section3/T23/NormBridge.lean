import NSFormalization.Section3.T23.Boundary
import NSFormalization.Section4.R41.NonDensityL1

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

/-- Inhomogeneous order lowering contracts every slice, including empty
realization infima. -/
theorem sobolevENorm_mono_order {s r : ℝ} (hsr : s ≤ r) (z : Space → Space) :
    sobolevENorm s z ≤ sobolevENorm r z := by
  apply le_iInf
  rintro ⟨A, hA⟩
  have hlow : IsSobolevDatum s z (lowerVectorL r s hsr A) := by
    intro i ψ
    change NSFormalization.Paper3.angularRealization s
      (NSFormalization.Paper3.angularOrderLowering r s hsr _) ψ = _
    rw [NSFormalization.Paper3.angularRealization_orderLowering]
    exact hA i ψ
  have hn : ‖lowerVectorL r s hsr A‖ₑ ≤ ‖A‖ₑ :=
    enorm_le_iff_norm_le.mpr
      (NSFormalization.Section4.R41.lowerVectorL_norm_le r s hsr A)
  exact (iInf_le (fun B : {B : NSFormalization.Paper3.RealVectorSobolev s //
      IsSobolevDatum s z B} => ‖B.1‖ₑ) ⟨_, hlow⟩).trans hn

end NSFormalization.Section3.T23
