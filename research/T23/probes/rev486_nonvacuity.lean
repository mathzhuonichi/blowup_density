import NSFormalization.Section3.T23.Lifespan

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T23

/-! Reviewer non-vacuity check: the canonical placement threshold is positive,
so its guarded scale interval has a concrete inhabitant. -/

example {U f : VelocityField} {p : PressureField} {K : Set Space}
    (place : DomainPlacementData U p f K) :
    place.ε₀ ∈ Ioc (0 : ℝ) place.ε₀ :=
  ⟨place.eps_pos, le_rfl⟩

example {U f : VelocityField} {p : PressureField} {K : Set Space}
    (place : DomainPlacementData U p f K) :
    ∃ ε : ℝ, ε ∈ Ioc (0 : ℝ) place.ε₀ :=
  ⟨place.ε₀, place.eps_pos, le_rfl⟩

/-! This is the exact family-scale guard used by all four U8 fields; in the
assembled API its premise is `BoundaryInsertionAPI.eps_pos`. -/
example {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ ε : ℝ, ε ∈ Ioc (0 : ℝ) ε₀ :=
  ⟨ε₀, hε₀, le_rfl⟩
