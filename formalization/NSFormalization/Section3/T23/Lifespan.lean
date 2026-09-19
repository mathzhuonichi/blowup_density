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

/-- Uniqueness on the domain and an interior witness exclude every longer
solution. In the smooth branch the sole extra analytic premise is scalar IBP. -/
theorem domainLifespan_eq_of_interior {ν T : ℝ} {Ω : Set Space}
    {a : SpatialField} {g : SpaceTimeField} (hν : 0 < ν)
    (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hI : IBP Ω)
    (u : ClassicalSolutionOmega ν Ω a g T)
    (hblow : ∀ M : ℝ, 0 < M → ∀ δ : ℝ, 0 < δ →
      ∃ t : ℝ, ∃ x : Space, t ∈ Ioo 0 T ∧ T - δ < t ∧ x ∈ Ω ∧ M < ‖u.velocity (t, x)‖) :
    domainMaximalLifespan ν Ω a g = ENNReal.ofReal T := by
  apply le_antisymm _ (domainLifespan_ge_horizon u)
  by_contra hcon
  have hcon' : ENNReal.ofReal T <
      ⨆ S : ℝ, ⨆ _ : Nonempty (ClassicalSolutionOmega ν Ω a g S), ENNReal.ofReal S :=
    not_le.mp hcon
  obtain ⟨S, hS⟩ := lt_iSup_iff.mp hcon'
  obtain ⟨⟨w⟩, hTS⟩ := lt_iSup_iff.mp hS
  have hTSr : T < S := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg u.horizon_pos.le).mp hTS
  obtain ⟨C, hC⟩ := w.speed_bound hb hTSr
  have hmax0 : (0 : ℝ) ≤ max C 0 := le_max_right _ _
  obtain ⟨t, x, ht, _, hx, hlarge⟩ :=
    hblow (max C 0 + 1) (by linarith) T u.horizon_pos
  have heq := velocity_eq_of_ibp hν hI ho hb u w
    (show t ∈ Ico 0 (min T S) from ⟨ht.1.le, by rw [min_eq_left hTSr.le]; exact ht.2⟩) hx
  rw [heq] at hlarge
  have hbound := hC t ⟨ht.1.le, ht.2.le⟩ x (subset_closure hx)
  have := le_max_left C 0
  linarith

end NSFormalization.Section3.T23
