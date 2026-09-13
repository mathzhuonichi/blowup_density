import NavierStokes.R3CompactIntegration
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiating spatial integrals with uniform compact support

Joint continuity on a compact time-space set supplies the dominating
function, including continuity at the initial time.
-/

noncomputable section
namespace NavierStokes.R3CompactParametricIntegral

open Set Filter MeasureTheory ProblemStatement
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Set ℝ} {F G : ℝ × Space → E} {K : Set Space}

omit [NormedSpace ℝ E] in
theorem continuous_slice (hF : ContinuousOn F (I ×ˢ (univ : Set Space)))
    {t : ℝ} (ht : t ∈ I) : Continuous (fun x => F (t, x)) := by
  rw [← continuousOn_univ]
  exact hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ _ => ⟨ht, trivial⟩)

omit [NormedSpace ℝ E] in
theorem compact_slice (hK : IsCompact K)
    (hs : ∀ t ∈ I, ∀ x ∉ K, F (t, x) = 0) {t : ℝ} (ht : t ∈ I) :
    HasCompactSupport (fun x => F (t, x)) := by
  apply HasCompactSupport.intro hK
  intro x hx
  exact hs t ht x hx

theorem integral_continuousOn (hI : IsCompact I) (hK : IsCompact K)
    (hF : ContinuousOn F (I ×ˢ (univ : Set Space)))
    (hs : ∀ t ∈ I, ∀ x ∉ K, F (t, x) = 0) :
    ContinuousOn (fun t => ∫ x : Space, F (t, x)) I := by
  obtain ⟨C, hC⟩ := (hI.prod hK).exists_bound_of_continuousOn
    (hF.mono (prod_mono Subset.rfl (subset_univ K)))
  apply continuousOn_of_dominated (bound := K.indicator (fun _ : Space => C))
  · intro t ht
    exact (continuous_slice hF ht).aestronglyMeasurable
  · intro t ht
    exact Eventually.of_forall fun x => by
      by_cases hx : x ∈ K
      · simpa only [indicator_of_mem hx] using hC (t, x) ⟨ht, hx⟩
      · simp [indicator_of_notMem hx, hs t ht x hx]
  · exact (integrable_indicator_iff hK.measurableSet).mpr
      (integrableOn_const (C := C) (μ := volume) hK.measure_ne_top)
  · exact Eventually.of_forall fun x =>
      hF.comp (continuous_id.prodMk continuous_const).continuousOn (fun _ ht => ⟨ht, trivial⟩)

theorem integral_continuousOn_open (hI : IsOpen I) (hK : IsCompact K)
    (hF : ContinuousOn F (I ×ˢ (univ : Set Space)))
    (hs : ∀ t ∈ I, ∀ x ∉ K, F (t, x) = 0) :
    ContinuousOn (fun t => ∫ x : Space, F (t, x)) I := by
  rw [hI.continuousOn_iff]
  intro t ht
  obtain ⟨ε, hε, hεI⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hI.mem_nhds ht)
  have hc := integral_continuousOn (isCompact_closedBall t ε) hK
    (hF.mono (prod_mono hεI Subset.rfl)) (fun r hr x hx => hs r (hεI hr) x hx)
  exact hc.continuousAt (Metric.closedBall_mem_nhds t hε)

theorem integral_hasDerivAt (hI : IsOpen I) (hK : IsCompact K)
    (hF : ContinuousOn F (I ×ˢ (univ : Set Space)))
    (hG : ContinuousOn G (I ×ˢ (univ : Set Space)))
    (hsF : ∀ t ∈ I, ∀ x ∉ K, F (t, x) = 0)
    (hsG : ∀ t ∈ I, ∀ x ∉ K, G (t, x) = 0)
    (hd : ∀ t ∈ I, ∀ x, HasDerivAt (fun s => F (s, x)) (G (t, x)) t)
    {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun s => ∫ x : Space, F (s, x)) (∫ x : Space, G (t, x)) t := by
  obtain ⟨ε, hε, hεI⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hI.mem_nhds ht)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall t ε).prod hK).exists_bound_of_continuousOn
    (hG.mono (prod_mono hεI (subset_univ K)))
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s x => F (s, x)) (F' := fun s x => G (s, x))
    (bound := K.indicator (fun _ : Space => C)) (Metric.ball_mem_nhds t hε)
    ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hI.mem_nhds ht] with s hs
    exact (continuous_slice hF hs).aestronglyMeasurable
  · exact (continuous_slice hF ht).integrable_of_hasCompactSupport (compact_slice hK hsF ht)
  · exact (continuous_slice hG ht).aestronglyMeasurable
  · exact Eventually.of_forall fun x s hs => by
      by_cases hx : x ∈ K
      · simpa only [indicator_of_mem hx] using hC (s, x) ⟨Metric.ball_subset_closedBall hs, hx⟩
      · simp [indicator_of_notMem hx, hsG s (hεI (Metric.ball_subset_closedBall hs)) x hx]
  · exact (integrable_indicator_iff hK.measurableSet).mpr
      (integrableOn_const (C := C) (μ := volume) hK.measure_ne_top)
  · exact Eventually.of_forall fun x s hs => hd s (hεI (Metric.ball_subset_closedBall hs)) x

theorem integral_hasDerivAt_of_contDiffOn (hI : IsOpen I) (hK : IsCompact K)
    (hF : ContDiffOn ℝ 1 F (I ×ˢ (univ : Set Space)))
    (hs : ∀ t ∈ I, ∀ x ∉ K, F (t, x) = 0) {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun s => ∫ x : Space, F (s, x))
      (∫ x : Space, deriv (fun s => F (s, x)) t) t := by
  let G : ℝ × Space → E := fun z => fderiv ℝ F z (1, 0)
  have ho : IsOpen (I ×ˢ (univ : Set Space)) := hI.prod isOpen_univ
  have hG : ContinuousOn G (I ×ˢ (univ : Set Space)) :=
    (hF.continuousOn_fderiv_of_isOpen ho le_rfl).clm_apply continuousOn_const
  have hd (s : ℝ) (hs' : s ∈ I) (x : Space) :
      HasDerivAt (fun r => F (r, x)) (G (s, x)) s := by
    have hfd : DifferentiableAt ℝ F (s, x) :=
      (hF.contDiffAt (ho.mem_nhds ⟨hs', mem_univ x⟩)).differentiableAt (by norm_num)
    exact hfd.hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))
  have he (s : ℝ) (hs' : s ∈ I) (x : Space) : deriv (fun r => F (r, x)) s = G (s, x) :=
    (hd s hs' x).deriv
  have hsG : ∀ s ∈ I, ∀ x ∉ K, G (s, x) = 0 := by
    intro s hs' x hx
    have hz : (fun r => F (r, x)) =ᶠ[𝓝 s] (fun _ => (0 : E)) := by
      filter_upwards [hI.mem_nhds hs'] with r hr
      exact hs r hr x hx
    rw [← he s hs' x, hz.deriv_eq, deriv_const]
  simp_rw [he t ht]
  exact integral_hasDerivAt hI hK hF.continuousOn hG hs hsG hd ht

end NavierStokes.R3CompactParametricIntegral
