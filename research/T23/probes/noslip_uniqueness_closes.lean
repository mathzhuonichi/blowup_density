import NSFormalization.Section3.T23.NoSlipUniqueness

open Set
open NSFormalization.Section3.T23
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)

-- The full U7 conclusion under precisely the explicit boundary IBP residual.
example : ∀ (ν : ℝ), 0 < ν →
    ∀ (Ω : Set Space), IsBoundedBoxOrSmoothDomain Ω → IBP Ω →
    ∀ (a' : SpatialField), a' ∈ initialClassOmega Ω →
    ∀ (f : SpaceTimeField), f ∈ forceClassOmega Ω →
    ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionOmega ν Ω a' f T₁)
      (u₂ : ClassicalSolutionOmega ν Ω a' f T₂),
    ∀ t ∈ Ico (0 : ℝ) (min T₁ T₂), ∀ x ∈ Ω,
      u₁.velocity (t, x) = u₂.velocity (t, x) := noSlip_uniqueness_of_ibp

-- This is deliberately not a declaration of unrestricted noSlip_uniqueness.
