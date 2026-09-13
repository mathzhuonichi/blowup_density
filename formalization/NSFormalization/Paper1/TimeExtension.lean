import NSFormalization.Paper1.LocalCutoff

/-! Smooth extension in time for a reference known only on its regular interval.
Multiplication by a time-only cutoff preserves spatial divergence. -/
noncomputable section
namespace NSFormalization.Paper1
open NavierStokes NavierStokes.ProblemStatement Set Filter
open scoped ContDiff Topology

def timeTruncation (v : VelocityField) (η : ℝ → ℝ) : VelocityField :=
  fun z => η z.1 • v z

/-- A smooth time switch supported in the regular interval makes an arbitrary
outside extension of the reference globally smooth. -/
theorem timeTruncation_smooth {v : VelocityField} {I : Set ℝ} (hI : IsOpen I)
    (hv : ContDiffOn ℝ ∞ v (I ×ˢ (univ : Set Space)))
    {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η) (hsupport : tsupport η ⊆ I) :
    ContDiff ℝ ∞ (timeTruncation v η) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases ht : z.1 ∈ I
  · exact ((hη.comp contDiff_fst).contDiffAt).smul
      ((hv z ⟨ht, mem_univ _⟩).contDiffAt ((hI.prod isOpen_univ).mem_nhds ⟨ht, mem_univ _⟩))
  · have hn : z.1 ∉ tsupport η := fun h => ht (hsupport h)
    have hevent : ∀ᶠ p : SpaceTime in 𝓝 z, p.1 ∉ tsupport η :=
      ((isClosed_tsupport η).isOpen_compl.preimage continuous_fst).mem_nhds hn
    apply (contDiffAt_const (c := (0 : Space))).congr_of_eventuallyEq
    filter_upwards [hevent] with p hp
    simp [timeTruncation, image_eq_zero_of_notMem_tsupport hp]

/-- No spatial divergence is introduced, including outside the original domain
where the truncated field vanishes identically on the whole spatial slice. -/
theorem timeTruncation_divergence {v : VelocityField} {I : Set ℝ}
    (hv : ContDiffOn ℝ ∞ v (I ×ˢ (univ : Set Space)))
    (hdiv : ∀ t ∈ I, ∀ x, spatialDivergence v t x = 0)
    {η : ℝ → ℝ} (hsupport : tsupport η ⊆ I) (t : ℝ) (x : Space) :
    spatialDivergence (timeTruncation v η) t x = 0 := by
  by_cases ht : t ∈ I
  · exact ResidualCalculus.time_smul_divergence_free v η t x
      ((SpatialCurl.contDiff_spatialSlice hv ht).differentiable (by simp) x) (hdiv t ht x)
  · have hη : η t = 0 := image_eq_zero_of_notMem_tsupport (fun h => ht (hsupport h))
    simp [timeTruncation, spatialDivergence, spatialDerivative, hη]

theorem timeTruncation_eq (v : VelocityField) (η : ℝ → ℝ) {t : ℝ} (hη : η t = 1)
    (x : Space) : timeTruncation v η (t, x) = v (t, x) := by simp [timeTruncation, hη]

/-- A reference regular on a finite open interval admits a globally smooth,
divergence-free extension agreeing throughout a smaller closed interval. -/
theorem exists_global_reference_extension {v : VelocityField} (T δ : ℝ) (hδ : 0 < δ)
    (hv : ContDiffOn ℝ ∞ v (Ioo (T - 2 * δ) (T + 2 * δ) ×ˢ (univ : Set Space)))
    (hdiv : ∀ t ∈ Ioo (T - 2 * δ) (T + 2 * δ), ∀ x, spatialDivergence v t x = 0) :
    ∃ V : VelocityField, ContDiff ℝ ∞ V ∧
      (∀ t x, spatialDivergence V t x = 0) ∧
      EqOn V v (Icc (T - δ) (T + δ) ×ˢ (univ : Set Space)) ∧
      (∀ t ∉ Ioo (T - 2 * δ) (T + 2 * δ), ∀ x, V (t, x) = 0) := by
  obtain ⟨η, hηsmooth, _hηcompact, hηone, hηsupport⟩ := exists_temporal_cutoff T δ hδ
  refine ⟨timeTruncation v η, timeTruncation_smooth isOpen_Ioo hv hηsmooth hηsupport,
    timeTruncation_divergence hv hdiv hηsupport, ?_, ?_⟩
  · intro z hz
    exact timeTruncation_eq v η (hηone hz.1) z.2
  · intro t ht x
    have hη : η t = 0 := image_eq_zero_of_notMem_tsupport (fun h => ht (hηsupport h))
    simp [timeTruncation, hη]

/-- The local background-removal lemma no longer needs global smoothness of
the original reference: a regular open neighborhood of the working time window
is sufficient. -/
theorem exists_local_background_removal_on {v : VelocityField} (T δ : ℝ) (hδ : 0 < δ)
    (hv : ContDiffOn ℝ ∞ v (Ioo (T - 4 * δ) (T + 4 * δ) ×ˢ (univ : Set Space)))
    (hdiv : ∀ t ∈ Ioo (T - 4 * δ) (T + 4 * δ), ∀ x, spatialDivergence v t x = 0)
    {K : Set Space} (hK : IsCompact K) {x₀ : Space} {R : ℝ}
    (hR : 0 < R) (hKR : K ⊆ Metric.ball x₀ R) :
    ∃ w : VelocityField, ∃ O : Set Space,
      ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧
      (∀ t x, spatialDivergence w t x = 0) ∧
      tsupport w ⊆ Ioo (T - 2 * δ) (T + 2 * δ) ×ˢ Metric.ball x₀ R ∧
      IsOpen O ∧ K ⊆ O ∧
      (∀ t ∈ Icc (T - δ) (T + δ), ∀ x ∈ O,
        ∀ᶠ y in 𝓝 x, v (t, y) + w (t, y) = 0) := by
  have h2δ : 0 < 2 * δ := by positivity
  obtain ⟨V, hVsmooth, hVdiv, hVeq, _hVzero⟩ :=
    exists_global_reference_extension T (2 * δ) h2δ
      (by simpa only [show 2 * (2 * δ) = 4 * δ by ring] using hv)
      (by simpa only [show 2 * (2 * δ) = 4 * δ by ring] using hdiv)
  obtain ⟨w, O, hwsmooth, hwcompact, hwdiv, hwsupport, hO, hKO, hzero⟩ :=
    exists_local_background_removal hVsmooth hVdiv hK hR hKR T δ hδ
  refine ⟨w, O, hwsmooth, hwcompact, hwdiv, hwsupport, hO, hKO, ?_⟩
  intro t ht x hx
  have heq : ∀ y, V (t, y) = v (t, y) := by
    intro y
    apply hVeq
    exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, mem_univ _⟩
  filter_upwards [hzero t ht x hx] with y hy
  simpa only [heq y] using hy

end NSFormalization.Paper1
