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

end NSFormalization.Section3.T23
