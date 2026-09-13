import NSFormalization.Paper3.SeparatedBochnerDensity
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! Positive-time temporal density, reusing Mathlib smooth approximation and
its small-set Lp estimate. The cutoff vanishes on a neighborhood of time zero. -/
noncomputable section
namespace NSFormalization.Paper3
open Set MeasureTheory
open scoped ContDiff ENNReal

abbrev positiveTimeMeasure : Measure ℝ := volume.restrict (Ioi 0)

def positiveTimeCutoff (δ : ℝ) (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.smoothTransition (t / δ - 1) * a t

 theorem positiveTimeCutoff_smooth (δ : ℝ) {a : ℝ → ℝ} (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (positiveTimeCutoff δ a) :=
  (Real.smoothTransition.contDiff.comp ((contDiff_id.div_const δ).sub contDiff_const)).mul ha

 theorem positiveTimeCutoff_compact (δ : ℝ) {a : ℝ → ℝ} (ha : HasCompactSupport a) :
    HasCompactSupport (positiveTimeCutoff δ a) := ha.mul_left

 theorem positiveTimeCutoff_support {δ : ℝ} (hδ : 0 < δ) (a : ℝ → ℝ) :
    tsupport (positiveTimeCutoff δ a) ⊆ Ioi 0 := by
  have hs : Function.support (positiveTimeCutoff δ a) ⊆ Ici δ := by
    intro t ht
    by_contra hn
    have hlt : t < δ := lt_of_not_ge hn
    have hc : t / δ - 1 ≤ 0 := by
      have := (div_le_one hδ).mpr hlt.le
      linarith
    exact ht (by simp [positiveTimeCutoff, Real.smoothTransition.zero_of_nonpos hc])
  exact (closure_minimal hs isClosed_Ici).trans (fun _ ht => lt_of_lt_of_le hδ ht)

/-- The existing uniform small-set Lp estimate controls the cutoff error. -/
theorem exists_positiveTimeCutoff_error (q : ℝ≥0∞) (hq : q ≠ ⊤)
    (a : ℝ → ℝ) (ha : Continuous a) (hac : HasCompactSupport a)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ eLpNorm (a - positiveTimeCutoff δ a) q positiveTimeMeasure ≤ ε := by
  obtain ⟨M, hM⟩ := hac.exists_bound_of_continuous ha
  obtain ⟨η, hη, hηbound⟩ := exists_eLpNorm_indicator_le
    (μ := positiveTimeMeasure) hq M hε
  let δ : ℝ := (η : ℝ) / 2
  have hδ : 0 < δ := by exact div_pos (by exact_mod_cast hη) (by norm_num)
  refine ⟨δ, hδ, ?_⟩
  have hb : eLpNorm ((Ioc 0 (2 * δ)).indicator (fun _ : ℝ => M)) q positiveTimeMeasure ≤ ε := by
    apply hηbound
    calc
      positiveTimeMeasure (Ioc 0 (2 * δ)) ≤ volume (Ioc 0 (2 * δ)) := Measure.restrict_apply_le _ _
      _ = ENNReal.ofReal (2 * δ) := by rw [Real.volume_Ioc]; simp
      _ = (η : ℝ≥0∞) := by
        rw [show 2 * δ = (η : ℝ) by dsimp [δ]; ring, ENNReal.ofReal_coe_nnreal]
  apply (eLpNorm_mono_ae ?_).trans hb
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htpos : 0 < t := ht
  by_cases hband : t ≤ 2 * δ
  · rw [Set.indicator_of_mem (show t ∈ Ioc (0 : ℝ) (2 * δ) from ⟨htpos, hband⟩)]
    have h0 := Real.smoothTransition.nonneg (t / δ - 1)
    have h1 := Real.smoothTransition.le_one (t / δ - 1)
    have heq : a t - positiveTimeCutoff δ a t =
        (1 - Real.smoothTransition (t / δ - 1)) * a t := by unfold positiveTimeCutoff; ring
    change ‖a t - positiveTimeCutoff δ a t‖ ≤ ‖M‖
    rw [heq, norm_mul, Real.norm_of_nonneg (by linarith)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (by linarith)).trans
      ((hM t).trans (le_abs_self M))
  · have hc : 1 ≤ t / δ - 1 := by
      have hd : 2 ≤ t / δ := (le_div_iff₀ hδ).mpr (by linarith)
      linarith
    simp [Pi.sub_apply, positiveTimeCutoff, Real.smoothTransition.one_of_one_le hc]

/-- Scalar time factors supported strictly inside the positive halfline are
dense in Lq on that halfline. -/
theorem dense_positive_temporal_factors (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq : q ≠ ⊤) :
    Dense {v : Lp ℝ q positiveTimeMeasure | ∃ a : ℝ → ℝ,
      v =ᵐ[positiveTimeMeasure] a ∧ HasCompactSupport a ∧ ContDiff ℝ ∞ a ∧
        tsupport a ⊆ Ioi 0} := by
  apply Dense.of_closure
  apply (Lp.dense_hasCompactSupport_contDiff (μ := positiveTimeMeasure) hq).mono
  rintro v ⟨a, hva, hac, ha⟩
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, herr⟩ := exists_positiveTimeCutoff_error q hq a ha.continuous hac
    (ε := ENNReal.ofReal (ε / 2)) (by positivity)
  let b := positiveTimeCutoff δ a
  have hbc : HasCompactSupport b := positiveTimeCutoff_compact δ hac
  have hb : ContDiff ℝ ∞ b := positiveTimeCutoff_smooth δ ha
  have hbm : MemLp b q positiveTimeMeasure := hb.continuous.memLp_of_hasCompactSupport hbc
  refine ⟨hbm.toLp b, ⟨b, hbm.coeFn_toLp, hbc, hb, positiveTimeCutoff_support hδ a⟩, ?_⟩
  rw [Lp.dist_def]
  have hae : ((v : ℝ → ℝ) - (hbm.toLp b : ℝ → ℝ)) =ᵐ[positiveTimeMeasure] (a - b) :=
    hva.sub hbm.coeFn_toLp
  rw [eLpNorm_congr_ae hae]
  exact (ENNReal.toReal_le_of_le_ofReal (by positivity) herr).trans_lt (by linarith)

end NSFormalization.Paper3
