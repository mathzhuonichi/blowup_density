import NSFormalization.Section4.A04.H1Restart

/-!
Reviewer mutation: widen the main restart-time interval from `Icc 0 S` to
`Icc (-1) S`.  Reusing the proved supplier must fail because it requires the
nonnegative restart-time guard used by `restart_force`.
-/
noncomputable section

open Set NavierStokes.ProblemStatement
open NSFormalization.Section4.A02
open NSFormalization.Section4.A04
open NSFormalization.Section4.D01 (sobolevENorm)
open scoped ENNReal

example (ν : ℝ) (hν : 0 < ν) (f : SpaceTimeField) (hf : MemForceR f)
    (S : ℝ) (hS : 0 ≤ S) (K : ℝ≥0∞) (hK : K ≠ ⊤) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t₀ ∈ Icc (-1 : ℝ) S,
      ∀ (a : SpatialField), a ∈ initialClassR → sobolevENorm 1 a ≤ K →
        ∃ w : ClassicalSolutionR ν a (timeShift t₀ f) δ,
          NSFormalization.Section4.A01.ManuscriptLocalRegularity
            ν a (timeShift t₀ f) δ w := by
  obtain ⟨δ, hδ, hr⟩ := h1RestartR ν hν f hf S hS K hK
  refine ⟨δ, hδ, ?_⟩
  intro t₀ ht₀ a ha hnorm
  exact hr t₀ ht₀ a ha hnorm
