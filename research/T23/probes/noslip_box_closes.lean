import NSFormalization.Section3.T23.NoSlipUniqueness

open Set MeasureTheory
open NSFormalization.Section3.T23
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)

-- Exact box U7 target, without added energy or integration premises.
example : ∀ (ν : ℝ), 0 < ν →
    ∀ (Ω : Set Space), IsBoxDomain Ω →
    ∀ (a' : SpatialField), a' ∈ initialClassOmega Ω →
    ∀ (f : SpaceTimeField), f ∈ forceClassOmega Ω →
    ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionOmega ν Ω a' f T₁)
      (u₂ : ClassicalSolutionOmega ν Ω a' f T₂),
    ∀ t ∈ Ico (0 : ℝ) (min T₁ T₂), ∀ x ∈ Ω,
      u₁.velocity (t, x) = u₂.velocity (t, x) := noSlip_uniqueness_box

example {Ω : Set Space} (hΩ : IsBoxDomain Ω) : IBP Ω := ibp_box hΩ

-- Off-origin, unequal side lengths: no unit-cube or centering restriction.
example : IBP {x : Space | ∀ i : Fin 3,
    (10 + (i : ℕ) : ℝ) < x i ∧ x i < 12 + 2 * (i : ℕ)} := by
  apply ibp_box
  refine ⟨(fun i => 10 + (i : ℕ)), (fun i => 12 + 2 * (i : ℕ)), ?_, rfl⟩
  intro i
  have : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _
  linarith
