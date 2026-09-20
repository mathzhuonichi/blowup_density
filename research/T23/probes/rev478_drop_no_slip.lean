import NSFormalization.Section3.T23.NoSlipUniqueness

open Set MeasureTheory
open NSFormalization.Section3.T23
open NavierStokes.ProblemStatement
open NavierStokesR3.ProblemStatement (navierStokesResidual)
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)

noncomputable section

-- Mutation: this is the canonical solution record with the `no_slip` field
-- removed, while retaining smoothness, initial data, divergence, momentum and
-- pressure normalization.
structure SolutionWithoutNoSlip (ν : ℝ) (Ω : Set Space) (a : SpatialField)
    (g : SpaceTimeField) (T : ℝ) where
  velocity : SpaceTimeField
  pressure : SpaceTimeScalar
  horizon_pos : 0 < T
  velocity_smooth : SmoothOnClosedSlab (Ico (0 : ℝ) T) Ω velocity
  pressure_smooth : SmoothOnClosedSlab (Ico (0 : ℝ) T) Ω pressure
  initial : ∀ x ∈ Ω, velocity (0, x) = a x
  divergence : ∀ t ∈ Ico (0 : ℝ) T, ∀ x ∈ Ω,
    spatialDivergence velocity t x = 0
  momentum : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x ∈ Ω,
    navierStokesResidual ν velocity pressure t x = g (t, x)
  pressure_gauge : ∀ t ∈ Ico (0 : ℝ) T,
    (∫ x in Ω, pressure (t, x)) = 0

-- The main statement with no-slip dropped. Reusing the reviewed proof must
-- fail because the weaker records do not supply the boundary cancellation.
theorem noSlip_uniqueness_box_without_no_slip : ∀ (ν : ℝ), 0 < ν →
    ∀ (Ω : Set Space), IsBoxDomain Ω →
    ∀ (a' : SpatialField), a' ∈ initialClassOmega Ω →
    ∀ (f : SpaceTimeField), f ∈ forceClassOmega Ω →
    ∀ (T₁ T₂ : ℝ) (u₁ : SolutionWithoutNoSlip ν Ω a' f T₁)
      (u₂ : SolutionWithoutNoSlip ν Ω a' f T₂),
    ∀ t ∈ Ico (0 : ℝ) (min T₁ T₂), ∀ x ∈ Ω,
      u₁.velocity (t, x) = u₂.velocity (t, x) := by
  intro ν hν Ω hΩ a' ha f hf T₁ T₂ u₁ u₂ t ht x hx
  exact noSlip_uniqueness_box ν hν Ω hΩ a' ha f hf T₁ T₂ u₁ u₂ t ht x hx
