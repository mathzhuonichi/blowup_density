import NSFormalization.Paper3.PositiveTemporalDensity
import NSFormalization.Paper3.PhysicalBochnerDensity

/-! Physical compact smooth density on positive time. Every representative has
compact support strictly inside `(0,∞) × Space`, hence vanishes near time zero. -/
noncomputable section
namespace NSFormalization.Paper3
open Set MeasureTheory NavierStokes.ProblemStatement
open scoped ContDiff ENNReal

/-- Actual compact spacetime representatives with support in positive time. -/
def positivePhysicalBochner (s : ℝ) (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    Submodule ℝ (Lp (SobolevHilbert s) q positiveTimeMeasure) where
  carrier := {v | ∃ (F : ℝ × Space → ℂ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F),
      tsupport F ⊆ {z | 0 < z.1} ∧
        v =ᵐ[positiveTimeMeasure] compactSobolevTimeSlice s F hF hc}
  zero_mem' := by
    refine ⟨0, contDiff_const, HasCompactSupport.zero, by simp, ?_⟩
    filter_upwards [Lp.coeFn_zero (SobolevHilbert s) q positiveTimeMeasure] with t ht
    rw [ht]
    change 0 = weightedFourierLp s 0
    rw [map_zero]
  add_mem' := by
    rintro v w ⟨F, hF, hFc, hFs, hv⟩ ⟨G, hG, hGc, hGs, hw⟩
    refine ⟨F + G, hF.add hG, hFc.add hGc,
      (tsupport_add F G).trans (union_subset hFs hGs), ?_⟩
    filter_upwards [Lp.coeFn_add v w, hv, hw] with t ht hvt hwt
    rw [ht, Pi.add_apply, hvt, hwt, compactSobolevTimeSlice_add]
  smul_mem' := by
    rintro c v ⟨F, hF, hFc, hFs, hv⟩
    refine ⟨c • F, hF.const_smul c, hFc.smul_left,
      (tsupport_smul_subset_right (fun _ => c) F).trans hFs, ?_⟩
    filter_upwards [Lp.coeFn_smul c v, hv] with t ht hvt
    rw [ht, Pi.smul_apply, hvt, compactSobolevTimeSlice_smul]

 theorem separatedLp_mem_positivePhysicalBochner (s : ℝ) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (ψ : SchwartzMap Space ℂ) (hψ : HasCompactSupport (ψ : Space → ℂ))
    (g : Lp ℝ q positiveTimeMeasure) (a : ℝ → ℝ)
    (hga : g =ᵐ[positiveTimeMeasure] a) (hac : HasCompactSupport a)
    (ha : ContDiff ℝ ∞ a) (has : tsupport a ⊆ Ioi 0) :
    separatedLp q (weightedFourierLp s ψ) g ∈ positivePhysicalBochner s q := by
  let F : ℝ × Space → ℂ := fun z => a z.1 • ψ z.2
  have hF : ContDiff ℝ ∞ F := (ha.comp contDiff_fst).smul ((ψ.smooth ⊤).comp contDiff_snd)
  have hFc : HasCompactSupport F := separated_physical_hasCompactSupport hac hψ
  have hs : tsupport F ⊆ Prod.fst ⁻¹' tsupport a := by
    apply closure_minimal ?_ ((isClosed_tsupport a).preimage continuous_fst)
    intro z hz
    apply subset_tsupport a
    intro hz0
    exact hz (by simp [F, hz0])
  refine ⟨F, hF, hFc, hs.trans (fun z hz => has hz), ?_⟩
  filter_upwards [separatedLp_ae q (weightedFourierLp s ψ) g, hga] with t ht hgat
  rw [ht, hgat]
  change a t • weightedFourierLp s ψ = weightedFourierLp s _
  rw [← map_smul]
  congr 1

/-- Density of actual physical spacetime C∞ compact representatives supported
strictly inside positive time, for every real order and finite q≥1. -/
theorem dense_positivePhysicalBochner (s : ℝ) (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq : q ≠ ⊤) :
    Dense (positivePhysicalBochner s q : Set (Lp (SobolevHilbert s) q positiveTimeMeasure)) := by
  have hd := dense_span_separatedLp (μ := positiveTimeMeasure) q hq
    (dense_compact_weightedFourierLp s) (dense_positive_temporal_factors q hq)
  apply hd.mono
  apply Submodule.span_le.mpr
  rintro v ⟨h, ⟨ψ, hψ, rfl⟩, g, ⟨a, hga, hac, ha, has⟩, rfl⟩
  exact separatedLp_mem_positivePhysicalBochner s q ψ hψ g a hga hac ha has

/-- The approximation comes from an original physical function with compact
support contained in `(0,∞) × Space`; no boundary trace or extension is assumed. -/
theorem exists_positive_physical_compact_smooth_approx (s : ℝ) (q : ℝ≥0∞)
    [Fact (1 ≤ q)] (hq : q ≠ ⊤) (f : Lp (SobolevHilbert s) q positiveTimeMeasure)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (F : ℝ × Space → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F),
      tsupport F ⊆ {z | 0 < z.1} ∧
      ‖f - ((memLp_compactSobolevTimeSlice s hF hc q).restrict (s := Ioi 0)).toLp
        (compactSobolevTimeSlice s F hF hc)‖ < ε := by
  obtain ⟨v, ⟨F, hF, hc, hFs, hv⟩, hdist⟩ :=
    Metric.mem_closure_iff.mp (dense_positivePhysicalBochner s q hq f) ε hε
  refine ⟨F, hF, hc, hFs, ?_⟩
  have heq : v = ((memLp_compactSobolevTimeSlice s hF hc q).restrict (s := Ioi 0)).toLp
      (compactSobolevTimeSlice s F hF hc) :=
    Lp.ext (hv.trans ((memLp_compactSobolevTimeSlice s hF hc q).restrict (s := Ioi 0)).coeFn_toLp.symm)
  simpa only [dist_eq_norm, heq] using hdist

end NSFormalization.Paper3
