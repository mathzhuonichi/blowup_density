import NSFormalization.Section3.T16.Assembly

/-! A solenoidal extension of a reference known only on an interior cylinder.
The extension is the curl of the radial potential times one fixed spatial bump. -/
noncomputable section
namespace NSFormalization.Section3.T23
open Set Filter Metric
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T16
open NSFormalization.Paper1.RadialPotential (timePotential)
open scoped ContDiff Topology

/-- Local smoothness and divergence suffice for a globally spatially smooth,
solenoidal extension agreeing on the smaller open ball. The cutoff is fixed,
independent of the eventual packet scale. -/
theorem exists_spatial_solenoidal_extension {v : VelocityField} {I : Set ℝ}
    {x₀ : Space} {r : ℝ} (hI : IsOpen I) (hr : 0 < r)
    (hv : ContDiffOn ℝ ∞ v (I ×ˢ ball x₀ r))
    (hdiv : ∀ t ∈ I, ∀ x ∈ ball x₀ r, spatialDivergence v t x = 0) :
    ∃ V : VelocityField,
      ContDiffOn ℝ ∞ V (I ×ˢ (univ : Set Space)) ∧
      (∀ t ∈ I, ∀ x, spatialDivergence V t x = 0) ∧
      EqOn V v (I ×ˢ ball x₀ (r / 2)) := by
  let χ : ContDiffBump x₀ := ⟨r / 2, 3 * r / 4, by positivity, by linarith⟩
  have hs : tsupport (χ : Space → ℝ) ⊆ ball x₀ r := by
    rw [χ.tsupport_eq]
    exact closedBall_subset_ball (by change 3 * r / 4 < r; linarith)
  let A : VelocityField := fun z => χ z.2 • timePotential v x₀ z
  have hA : ContDiffOn ℝ ∞ A (I ×ˢ (univ : Set Space)) :=
    contDiffOn_bumpSmul hI (timePotential_contDiffOn_ball hI hv) χ.contDiff hs
  refine ⟨SpatialCurl.spatialCurl A,
    SpatialCurl.contDiffOn_spatialCurl hA (by simp), ?_, ?_⟩
  · intro t ht x
    exact SpatialCurl.spatialDivergence_spatialCurl A t x
      ((SpatialCurl.contDiff_spatialSlice hA ht).contDiffAt.of_le (by norm_num))
  · rintro ⟨t, x⟩ ⟨ht, hx⟩
    have hχ : ∀ᶠ y in 𝓝 x, χ y = 1 := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact χ.one_of_mem_closedBall (ball_subset_closedBall hy)
    change SpatialCurl.curl (fun y => χ y • timePotential v x₀ (t, y)) x = v (t, x)
    rw [SpatialCurl.curl_cutoff_eq hχ]
    exact spatialCurl_timePotential_on_ball hv hdiv ht
      (ball_subset_ball (by linarith : r / 2 ≤ r) hx)

/-- A fixed time cutoff turns the spatial extension into a globally smooth
solenoidal field, retaining the reference on a closed window around `T`. -/
theorem exists_solenoidal_window_extension {v : VelocityField}
    {x₀ : Space} {r T δ : ℝ} (hr : 0 < r) (hT : 0 < T) (hδ : 0 < δ)
    (hv : ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ ball x₀ r))
    (hdiv : ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ ball x₀ r,
      spatialDivergence v t x = 0) :
    ∃ V : VelocityField, ContDiff ℝ ∞ V ∧
      (∀ t x, spatialDivergence V t x = 0) ∧
      EqOn V v (Icc (T - min T δ / 2) (T + min T δ / 2) ×ˢ ball x₀ (r / 2)) := by
  obtain ⟨W, hW, hWdiv, hWeq⟩ := exists_spatial_solenoidal_extension isOpen_Ioo hr hv hdiv
  let m := min T δ
  have hm : 0 < m := lt_min hT hδ
  have hmT : m ≤ T := min_le_left _ _
  have hmδ : m ≤ δ := min_le_right _ _
  let χ : ContDiffBump T := ⟨m / 2, 3 * m / 4, by positivity, by linarith⟩
  have hs : tsupport (χ : ℝ → ℝ) ⊆ Ioo (0 : ℝ) (T + δ) := by
    rw [χ.tsupport_eq]
    intro t ht
    change dist t T ≤ 3 * m / 4 at ht
    rw [Real.dist_eq, abs_le] at ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨NSFormalization.Paper1.timeTruncation W χ,
    NSFormalization.Paper1.timeTruncation_smooth isOpen_Ioo hW χ.contDiff hs,
    NSFormalization.Paper1.timeTruncation_divergence hW hWdiv hs, ?_⟩
  rintro ⟨t, x⟩ ⟨ht, hx⟩
  have ht' : t ∈ Ioo (0 : ℝ) (T + δ) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hc : χ t = 1 := by
    apply χ.one_of_mem_closedBall
    change dist t T ≤ m / 2
    rw [Real.dist_eq, abs_le]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rw [NSFormalization.Paper1.timeTruncation_eq W χ hc x]
  exact hWeq ⟨ht', hx⟩

/-- Equality of local references on the radial cylinder gives equality of the
entire physical correction, including outside that cylinder. -/
theorem physicalCorrection_eq_of_cylinder (v V : VelocityField) (x₀ : Space)
    (T ε r : ℝ) (θ : Space → ℝ) (η : ℝ → ℝ) {I : Set ℝ}
    (heq : EqOn v V (I ×ˢ ball x₀ r))
    (ht : tsupport (NSFormalization.Paper1.CorrectionProfile.temporalCutoff η T ε) ⊆ I)
    (hs : tsupport (NSFormalization.Paper1.CorrectionProfile.spatialCutoff θ x₀ ε) ⊆ ball x₀ r) :
    NSFormalization.Paper1.CorrectionProfile.physicalCorrection v x₀ T θ η ε =
      NSFormalization.Paper1.CorrectionProfile.physicalCorrection V x₀ T θ η ε := by
  funext z
  have hinner : (fun y : Space =>
      (NSFormalization.Paper1.CorrectionProfile.temporalCutoff η T ε z.1 *
        NSFormalization.Paper1.CorrectionProfile.spatialCutoff θ x₀ ε y) •
          timePotential v x₀ (z.1, y)) =
      (fun y : Space =>
      (NSFormalization.Paper1.CorrectionProfile.temporalCutoff η T ε z.1 *
        NSFormalization.Paper1.CorrectionProfile.spatialCutoff θ x₀ ε y) •
          timePotential V x₀ (z.1, y)) := by
    funext y
    by_cases hc : NSFormalization.Paper1.CorrectionProfile.temporalCutoff η T ε z.1 *
        NSFormalization.Paper1.CorrectionProfile.spatialCutoff θ x₀ ε y = 0
    · simp only [hc, zero_smul]
    · have htc := (mul_ne_zero_iff.mp hc).1
      have hsc := (mul_ne_zero_iff.mp hc).2
      have hyt := ht (subset_tsupport _ htc)
      have hy := hs (subset_tsupport _ hsc)
      have hp : timePotential v x₀ (z.1, y) = timePotential V x₀ (z.1, y) := by
        apply timePotential_congr_segment
        intro ρ hρ
        apply heq
        refine ⟨hyt, ?_⟩
        rw [mem_ball, dist_eq_norm]
        have hh : x₀ + ρ • (y - x₀) - x₀ = ρ • (y - x₀) := by abel
        rw [hh, norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ.1]
        have hyn : ‖y - x₀‖ < r := by simpa only [mem_ball, dist_eq_norm] using hy
        nlinarith [norm_nonneg (y - x₀), hρ.2]
      rw [hp]
  change -SpatialCurl.curl _ z.2 = -SpatialCurl.curl _ z.2
  rw [hinner]

end NSFormalization.Section3.T23
