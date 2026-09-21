import NSFormalization.Source.BoundedViscosityUniqueness
import NavierStokes.R3.CompactComparisonBounds

/-! The complete compact blowup theorem, with nonexistence for the same force. -/

noncomputable section
namespace NSFormalization.Source
open Set MeasureTheory NavierStokesR3 NavierStokesR3.ProblemStatement
open scoped ContDiff

/-- Every positive-viscosity compact candidate excludes a global smooth
solution with the same force, zero datum and uniformly bounded kinetic energy. -/
theorem candidate_excludes_global_solution {ν : ℝ} (hν : 0 < ν)
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (h : CandidateProperties ν u p f K) :
    ¬ Nonempty (GlobalFiniteEnergySolution ν f) := by
  rintro ⟨v⟩
  have heq : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x, u (t, x) = v.velocity (t, x) := by
    intro t ht x
    by_cases ht0 : t = 0
    · subst t
      exact (h.zero_initial_velocity x).trans (v.zero_initial_velocity x).symm
    have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have hpre : Comparison.slab 0 t ⊆ preSingularDomain :=
      fun _ hz => ⟨⟨hz.1.1, hz.1.2.trans_lt ht.2⟩, hz.2⟩
    have hfuture : Comparison.slab 0 t ⊆ futureDomain :=
      fun _ hz => ⟨hz.1.1, hz.2⟩
    have hu := h.velocity_smooth.mono hpre
    have hsupp : ∀ s ∈ Icc (0 : ℝ) t,
        tsupport (fun y => u (s, y)) ⊆ K :=
      fun s hs => h.velocity_support s ⟨hs.1, hs.2.trans_lt ht.2⟩
    obtain ⟨G, hG0, hG⟩ := CompactComparisonBounds.exists_gradient_bound
      htpos hu h.support_compact hsupp
    have hcompact : Icc (0 : ℝ) t ×ˢ K ⊆ Comparison.slab 0 t :=
      fun _ hz => ⟨hz.1, mem_univ _⟩
    obtain ⟨B, hB⟩ := (isCompact_Icc.prod h.support_compact).exists_bound_of_continuousOn
      (hu.continuousOn.mono hcompact)
    have hbound : ∀ s ∈ Icc (0 : ℝ) t, ∀ y, ‖u (s, y)‖ ≤ max B 0 := by
      intro s hs y
      by_cases hy : y ∈ K
      · exact (hB (s, y) ⟨hs, hy⟩).trans (le_max_left _ _)
      · have hz : u (s, y) = 0 :=
          image_eq_zero_of_notMem_tsupport (f := fun y => u (s, y))
            (fun hy' => hy (hsupp s hs hy'))
        simpa only [hz, norm_zero] using le_max_right B 0
    have hagree := BoundedViscosityUniqueness.classical_uniqueness_on_Icc htpos hν
      hu (v.velocity_smooth.mono hfuture) (h.pressure_smooth.mono hpre)
      (v.pressure_smooth.mono hfuture)
      (h.energy_bounded.mono (fun _ hs => ⟨hs.1, hs.2.trans_lt ht.2⟩))
      (v.energy_bounded.mono (fun _ hs => hs.1))
      (le_max_right B 0) hbound hG0 hG
      (fun s hs => h.divergence_free s ⟨hs.1.le, hs.2.trans ht.2⟩)
      (fun s hs => v.divergence_free s hs.1.le)
      (fun s hs y => (h.navier_stokes s ⟨hs.1, hs.2.trans ht.2⟩ y).trans
        (v.navier_stokes s hs.1 y).symm)
      (fun y => (h.zero_initial_velocity y).trans (v.zero_initial_velocity y).symm)
    exact hagree t ⟨ht.1, le_rfl⟩ x
  have hsub : Icc (0 : ℝ) 1 ×ˢ K ⊆ futureDomain :=
    fun _ hz => ⟨hz.1.1, mem_univ _⟩
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod h.support_compact).exists_bound_of_continuousOn
    (v.velocity_smooth.continuousOn.mono hsub)
  have hpos : 0 < max M 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨t, x, ht, _, hlarge⟩ := h.speed_unbounded (max M 1) hpos 1 zero_lt_one
  have hx : x ∈ K := by
    by_contra hnot
    have hz : u (t, x) = 0 := image_eq_zero_of_notMem_tsupport (f := fun x => u (t, x))
      (fun hx' => hnot (h.velocity_support t ⟨ht.1.le, ht.2⟩ hx'))
    rw [hz, norm_zero] at hlarge
    exact (not_lt_of_ge hpos.le) hlarge
  have hb := hM (t, x) ⟨⟨ht.1.le, ht.2.le⟩, hx⟩
  rw [heq t ⟨ht.1.le, ht.2⟩ x] at hlarge
  exact (not_lt_of_ge (hb.trans (le_max_left M 1))) hlarge

/-- Theorem 1.1 in full: one candidate and its same-force nonexistence
conclusion, for every positive viscosity, with singular time fixed at one. -/
theorem source_breakdown : breakdownStatement := by
  intro ν hν
  obtain ⟨u, p, f, K, h, _, _⟩ := selected_packet_every_viscosity hν
  exact ⟨u, p, f, K, h, candidate_excludes_global_solution hν h⟩

end NSFormalization.Source
