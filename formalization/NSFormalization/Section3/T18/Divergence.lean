import NSFormalization.Section3.T18.Kinematics
import NSFormalization.Section3.T16.LatticeLift

/-! T18 U4: divergence of the inserted velocity and its difference.
Spatial slices of slab smoothness are differentiable even at time zero,
so divergence additivity applies on the entire half-open time interval. -/

noncomputable section
namespace NSFormalization.Section3.T18
open Set
open scoped ContDiff
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T15
open NSFormalization.Section4.A02 (SpaceTimeField)

/-- Restriction to a spatial slice also works at the closed time endpoint. -/
theorem spatial_slice_differentiable {u : SpaceTimeField} {T t : ℝ}
    (hu : ContDiffOn ℝ ∞ u (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    (ht : t ∈ Ico 0 T) (x : Space) :
    DifferentiableAt ℝ (fun y : Space ↦ u (t, y)) x := by
  have hs : ContDiff ℝ ∞ (fun y : Space ↦ u (t, y)) :=
    hu.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun y ↦ ⟨ht, mem_univ y⟩)
  exact (hs.differentiable (by simp)).differentiableAt

theorem incompressible (data : InsertionData) : ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
    ∀ t ∈ Ico (0 : ℝ) data.place.T, ∀ x : Space,
      spatialDivergence (velocity data ε) t x = 0 := by
  intro ε hε t ht x
  obtain ⟨S, hv, _⟩ := data.scaling.solution ε (scaling_range data hε)
  have hr := spatial_slice_differentiable data.reference.velocity_smooth (reference_time data ht) x
  have hc := spatial_slice_differentiable
    (data.correction.potential.correction_smooth ε (correction_range data hε)).contDiffOn ht x
  have hp := spatial_slice_differentiable (hv ▸ S.velocity_smooth) ht x
  unfold velocity
  rw [NSFormalization.Section3.T16.spatialDivergence_add (hr.add hc) hp,
    NSFormalization.Section3.T16.spatialDivergence_add hr hc,
    data.reference.divergence t (reference_time data ht) x,
    data.correction.potential.correction_divergence_free ε (correction_range data hε) t x,
    ← hv, S.divergence t ht x]
  simp

theorem velocityDifference_divFree (data : InsertionData) : ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
    ∀ t ∈ Ico (0 : ℝ) data.place.T, ∀ x : Space,
      spatialDivergence (fun z ↦ velocity data ε z - data.reference.velocity z) t x = 0 := by
  intro ε hε t ht x
  have hu := spatial_slice_differentiable (velocity_smooth data ε hε) ht x
  have hv := spatial_slice_differentiable data.reference.velocity_smooth (reference_time data ht) x
  have hadd := NSFormalization.Section3.T16.spatialDivergence_add
    (u := fun z ↦ velocity data ε z - data.reference.velocity z)
    (v := data.reference.velocity) (hu.sub hv) hv
  have heq : (fun z ↦ (velocity data ε z - data.reference.velocity z) +
      data.reference.velocity z) = velocity data ε := by
    funext z
    exact sub_add_cancel _ _
  rw [heq, incompressible data ε hε t ht x,
    data.reference.divergence t (reference_time data ht) x, add_zero] at hadd
  exact hadd.symm
end NSFormalization.Section3.T18
