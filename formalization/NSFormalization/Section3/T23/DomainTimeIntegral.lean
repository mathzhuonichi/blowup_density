import NSFormalization.Section3.T23.NoSlipUniqueness
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Differentiation under a bounded-domain integral from closed-slab smoothness. -/
noncomputable section
namespace NSFormalization.Section3.T23
open Set MeasureTheory Filter
open NavierStokes.ProblemStatement
open scoped ContDiff Topology

/-- Joint continuity on a compact slab gives continuity of the domain integral. -/
theorem domainIntegral_continuousOn {Ω : Set Space} (hΩ : Bornology.IsBounded Ω)
    (hm : MeasurableSet Ω) {I : Set ℝ} (hI : IsCompact I) {F : SpaceTime → ℝ}
    (hF : ContinuousOn F (I ×ˢ closure Ω)) :
    ContinuousOn (fun t => ∫ x in Ω, F (t, x)) I := by
  have : IsFiniteMeasure (volume.restrict Ω) :=
    ⟨by simpa using hΩ.measure_lt_top (μ := volume)⟩
  obtain ⟨C, hC⟩ := (hI.prod hΩ.isCompact_closure).exists_bound_of_continuousOn hF
  apply continuousOn_of_dominated (bound := fun _ : Space => C)
  · intro t ht
    exact ((hF.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x hx => ⟨ht, subset_closure hx⟩)).aestronglyMeasurable hm)
  · intro t ht
    filter_upwards [ae_restrict_mem hm] with x hx
    exact hC (t, x) ⟨ht, subset_closure hx⟩
  · exact integrable_const C
  · filter_upwards [ae_restrict_mem hm] with x hx
    exact hF.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => ⟨ht, subset_closure hx⟩)

/-- A continuous time derivative on compact subslabs justifies differentiation
under the domain integral. The derivative is pointwise, not an energy premise. -/
theorem domainIntegral_hasDerivAt {Ω : Set Space} (hΩ : Bornology.IsBounded Ω)
    (hm : MeasurableSet Ω) {I : Set ℝ} (hI : IsOpen I) {F G : SpaceTime → ℝ}
    (hF : ContinuousOn F (I ×ˢ closure Ω))
    (hG : ContinuousOn G (I ×ˢ closure Ω))
    (hd : ∀ t ∈ I, ∀ x ∈ closure Ω, HasDerivAt (fun s => F (s, x)) (G (t, x)) t)
    {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun s => ∫ x in Ω, F (s, x)) (∫ x in Ω, G (t, x)) t := by
  have : IsFiniteMeasure (volume.restrict Ω) :=
    ⟨by simpa using hΩ.measure_lt_top (μ := volume)⟩
  obtain ⟨ε, hε, hεI⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hI.mem_nhds ht)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall t ε).prod hΩ.isCompact_closure).exists_bound_of_continuousOn
    (hG.mono (Set.prod_mono hεI Subset.rfl))
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (x₀ := t)
    (μ := volume.restrict Ω) (F := fun s x => F (s, x)) (F' := fun s x => G (s, x))
    (bound := fun _ => C) (Metric.ball_mem_nhds _ hε) ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hI.mem_nhds ht] with s hs
    exact (hF.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x hx => ⟨hs, subset_closure hx⟩)).aestronglyMeasurable hm
  · exact ((hF.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hx => ⟨ht, hx⟩)).integrableOn_compact hΩ.isCompact_closure).mono_set subset_closure
  · exact (hG.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x hx => ⟨ht, subset_closure hx⟩)).aestronglyMeasurable hm
  · filter_upwards [ae_restrict_mem hm] with x hx
    intro s hs
    exact hC (s, x) ⟨Metric.ball_subset_closedBall hs, subset_closure hx⟩
  · exact integrable_const C
  · filter_upwards [ae_restrict_mem hm] with x hx
    intro s hs
    exact hd s (hεI (Metric.ball_subset_closedBall hs)) x (subset_closure hx)

/-- The closed-slab convention supplies ordinary spacetime smoothness. -/
theorem SmoothOnClosedSlab.contDiffAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Set ℝ} {Ω : Set Space} {F : SpaceTime → E}
    (hF : SmoothOnClosedSlab I Ω F) {z : SpaceTime} (hz : z ∈ I ×ˢ closure Ω) :
    ContDiffAt ℝ ∞ F z := by
  obtain ⟨N, hN, hsub, hs⟩ := hF
  exact hs.contDiffAt (hN.mem_nhds (hsub hz))

/-- Smooth integrands have the expected time derivative under the domain integral. -/
theorem SmoothOnClosedSlab.hasDerivAt_integral {Ω : Set Space}
    (hΩ : Bornology.IsBounded Ω) (hm : MeasurableSet Ω) {I : Set ℝ} (hI : IsOpen I)
    {F : SpaceTime → ℝ} (hF : SmoothOnClosedSlab I Ω F) {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun s => ∫ x in Ω, F (s, x))
      (∫ x in Ω, deriv (fun s => F (s, x)) t) t := by
  let G : SpaceTime → ℝ := fun z => fderiv ℝ F z (1, 0)
  have hd (s : ℝ) (hs : s ∈ I) (x : Space) (hx : x ∈ closure Ω) :
      HasDerivAt (fun r => F (r, x)) (G (s, x)) s :=
    ((hF.contDiffAt ⟨hs, hx⟩).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))
  have h := domainIntegral_hasDerivAt hΩ hm hI
    (fun z hz => (hF.contDiffAt hz).continuousAt.continuousWithinAt)
    (show ContinuousOn G (I ×ˢ closure Ω) from fun z hz =>
      (((hF.contDiffAt hz).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).continuousAt.continuousWithinAt)
    hd ht
  convert h using 1
  apply setIntegral_congr_fun hm
  intro x hx
  exact (hd t ht x (subset_closure hx)).deriv
end NSFormalization.Section3.T23
