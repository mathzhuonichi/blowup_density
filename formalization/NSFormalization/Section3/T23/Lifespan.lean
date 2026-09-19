import NSFormalization.Section3.T23.InteriorBlowup

/-! T23 U8: compact-domain lifespan and maximality. -/

noncomputable section
namespace NSFormalization.Section3.T23
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)

/-- A longer solution is uniformly bounded on the compact terminal slab,
including the boundary of the domain. -/
theorem ClassicalSolutionOmega.speed_bound {ν S T : ℝ} {Ω : Set Space}
    {a : SpatialField} {g : SpaceTimeField}
    (w : ClassicalSolutionOmega ν Ω a g S) (hΩ : Bornology.IsBounded Ω) (hTS : T < S) :
    ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ closure Ω, ‖w.velocity (t, x)‖ ≤ C := by
  obtain ⟨N, _hN, hsub, hs⟩ := w.velocity_smooth
  have hsub' : Icc (0 : ℝ) T ×ˢ closure Ω ⊆ N := by
    intro z hz
    exact hsub ⟨⟨hz.1.1, hz.1.2.trans_lt hTS⟩, hz.2⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hΩ.isCompact_closure).exists_bound_of_continuousOn
    (hs.continuousOn.mono hsub')
  exact ⟨C, fun t ht x hx => hC (t, x) ⟨ht, hx⟩⟩

/-- Every actual solution horizon contributes to the defining supremum. -/
theorem domainLifespan_ge_horizon {ν T : ℝ} {Ω : Set Space}
    {a : SpatialField} {g : SpaceTimeField} (w : ClassicalSolutionOmega ν Ω a g T) :
    ENNReal.ofReal T ≤ domainMaximalLifespan ν Ω a g := by
  exact le_iSup_of_le T (le_iSup_of_le (Nonempty.intro w) le_rfl)

end NSFormalization.Section3.T23
