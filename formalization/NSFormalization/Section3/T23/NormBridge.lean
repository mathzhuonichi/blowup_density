import NSFormalization.Section3.T23.Boundary
import NSFormalization.Section4.R41.NonDensityL1
import NSFormalization.Section3.T22.OrderZero

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

/-- Lowering also contracts the quotient norm: every extension at the higher
order lowers to an extension of the same domain distribution. -/
theorem domainSobolevENorm_mono_order (Ω : Set Space) {s r : ℝ} (hsr : s ≤ r)
    (z : NSFormalization.Section3.T22.DomainFunctional Ω) :
    NSFormalization.Section3.T22.domainSobolevENorm Ω s z ≤
      NSFormalization.Section3.T22.domainSobolevENorm Ω r z := by
  apply le_iInf
  rintro ⟨A, hA⟩
  have hlow : NSFormalization.Section3.T22.restrictDatum Ω s (lowerVectorL r s hsr A) = z := by
    rw [← hA]
    funext i ψ
    change NSFormalization.Paper3.angularRealization s
      (NSFormalization.Paper3.angularOrderLowering r s hsr _) ψ.1 = _
    rw [NSFormalization.Paper3.angularRealization_orderLowering]
    rfl
  have hn : ‖lowerVectorL r s hsr A‖ₑ ≤ ‖A‖ₑ :=
    enorm_le_iff_norm_le.mpr
      (NSFormalization.Section4.R41.lowerVectorL_norm_le r s hsr A)
  exact (iInf_le (fun B : {B : NSFormalization.Paper3.RealVectorSobolev s //
      NSFormalization.Section3.T22.restrictDatum Ω s B = z} => ‖B.1‖ₑ)
      ⟨_, hlow⟩).trans hn

/-- Minkowski on actual realizing paths. Continuity and nonnegative order
supply the Schwartz-pairing integrability needed by datum addition. -/
theorem forceSobolevENorm_add_le_of_continuous {s : ℝ} (hs : 0 ≤ s)
    (f g : VelocityField)
    (hf : ∀ t, 0 ≤ t → Continuous (fun x => f (t, x)))
    (hg : ∀ t, 0 ≤ t → Continuous (fun x => g (t, x))) :
    forceSobolevENorm 1 s (fun z => f z + g z) ≤
      forceSobolevENorm 1 s f + forceSobolevENorm 1 s g := by
  unfold forceSobolevENorm
  rw [ENNReal.iInf_add]
  apply le_iInf
  rintro ⟨F, hF, hmF⟩
  rw [ENNReal.add_iInf]
  apply le_iInf
  rintro ⟨G, hG, hmG⟩
  have hsum : IsSobolevPath s (fun z => f z + g z) (fun t => F t + G t) := by
    intro t ht
    exact isSobolevDatum_add
      (schwartzPairable_of_isSobolevDatum hs (hf t ht) (hF t ht))
      (schwartzPairable_of_isSobolevDatum hs (hg t ht) (hG t ht))
      (hF t ht) (hG t ht)
  refine (iInf_le _ ⟨_, hsum, hmF.add hmG⟩).trans ?_
  exact eLpNorm_add_le hmF hmG le_rfl

/-- The literal negative-order zero-extension estimate against its physical
L² norm; square integrability is an honest realization hypothesis. -/
theorem sobolevENorm_zeroExtension_nonpos_le_L2 (Ω : Set Space) {s : ℝ}
    (hs : s ≤ 0) (z : Space → Space)
    (hz : MemLp (NSFormalization.Section3.T22.zeroExtension Ω z) 2 volume) :
    sobolevENorm s (NSFormalization.Section3.T22.zeroExtension Ω z) ≤
      eLpNorm (NSFormalization.Section3.T22.zeroExtension Ω z) 2 volume := by
  exact (sobolevENorm_mono_order hs _).trans_eq
    (NSFormalization.Section3.T22.sobolevENorm_zero_eq_eLpNorm hz)

end NSFormalization.Section3.T23
