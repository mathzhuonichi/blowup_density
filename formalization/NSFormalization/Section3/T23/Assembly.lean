import NSFormalization.Section3.T23.SpatialExtension
import NSFormalization.Section3.T23.MatchingSupplier

/-! U9 preparation. The full boundary API is not yet assembled. -/
noncomputable section
namespace NSFormalization.Section3.T23
open Set Filter Metric
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T16
open NSFormalization.Paper1.RadialPotential (timePotential)
open scoped ContDiff Topology

/-- Preserve any prescribed inner radius, using the positive outer margin. -/
theorem exists_spatial_solenoidal_extension_between {v : VelocityField} {I : Set ℝ}
    {x₀ : Space} {r s : ℝ} (hI : IsOpen I) (hs : 0 < s) (hsr : s < r)
    (hv : ContDiffOn ℝ ∞ v (I ×ˢ ball x₀ r))
    (hdiv : ∀ t ∈ I, ∀ x ∈ ball x₀ r, spatialDivergence v t x = 0) :
    ∃ V : VelocityField,
      ContDiffOn ℝ ∞ V (I ×ˢ (univ : Set Space)) ∧
      (∀ t ∈ I, ∀ x, spatialDivergence V t x = 0) ∧
      EqOn V v (I ×ˢ ball x₀ s) := by
  let χ : ContDiffBump x₀ := ⟨s, (s + r) / 2, hs, by linarith⟩
  have hs : tsupport (χ : Space → ℝ) ⊆ ball x₀ r := by
    rw [χ.tsupport_eq]
    exact closedBall_subset_ball (by change (s + r) / 2 < r; linarith)
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
      (ball_subset_ball (by linarith : s ≤ r) hx)


/-- The existing U3 core at the literal supplier cutoff would require global
agreement of radial potentials, beyond agreement on the interior cylinder. -/
theorem supplierCutoff_core_requires_global_potential
    {ν : ℝ} {u v : VelocityField} {K : Set Space}
    (C : WholeSpaceCorrectionAPI ν u K)
    (h : LocalCorrectionCore v u K C.x₀ C.r C.T C.δ C.supplierCutoff) :
    C.potential = timePotential v C.x₀ := by
  funext z
  exact h.potential_formula z.1 z.2

end NSFormalization.Section3.T23
