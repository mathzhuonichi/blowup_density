import NSFormalization.Section3.T23.DifferenceEnergy
import NSFormalization.Section3.T23.BoundaryIntegration

/-! No-slip velocity uniqueness with the boundary identity discharged.
The `of_ibp` and box variants remain available as reusable intermediate lemmas. -/
noncomputable section
namespace NSFormalization.Section3.T23
open Set NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)

/-- No-slip uniqueness on the manuscript domain class, without an IBP premise. -/
theorem noSlip_uniqueness : ∀ (ν : ℝ), 0 < ν →
    ∀ (Ω : Set Space), IsBoundedBoxOrSmoothDomain Ω →
    ∀ (a' : SpatialField), a' ∈ initialClassOmega Ω →
    ∀ (f : SpaceTimeField), f ∈ forceClassOmega Ω →
    ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionOmega ν Ω a' f T₁)
      (u₂ : ClassicalSolutionOmega ν Ω a' f T₂),
    ∀ t ∈ Ico (0 : ℝ) (min T₁ T₂), ∀ x ∈ Ω,
      u₁.velocity (t, x) = u₂.velocity (t, x) := by
  intro ν hν Ω hΩ
  exact noSlip_uniqueness_of_ibp ν hν Ω hΩ (ibp_boundedDomain hΩ)

end NSFormalization.Section3.T23
