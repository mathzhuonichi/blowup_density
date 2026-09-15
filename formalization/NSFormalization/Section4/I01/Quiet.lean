import NSFormalization.Source.ViscosityPacket

/-!
# The initial quiet interval of the packet

Lemma 2.2 of `paper/sections/02-preliminaries.tex:127-153` argues: "The temporal
support of `F` is a compact subset of `(0,∞)`, so `F = 0` on `[0,τ]` for some
`τ > 0`."  That step is carried out here for an arbitrary force with compact
positive-time support, and then combined with the early vanishing of the
selected packet's velocity and pressure into one closed initial interval.

Nothing in this file assumes existence of a packet: every statement is
conditional on the source hypotheses it names.
-/

noncomputable section

namespace NSFormalization.Section4.I01

open Set
open NavierStokes.ProblemStatement
open NavierStokesR3.ProblemStatement (CompactPositiveTimeSupport CandidateProperties)

/-- Compactness of the force's spacetime support inside `{t > 0}` produces a
closed initial interval on which the force vanishes: the time coordinate
attains a strictly positive minimum on the support.  This is the manuscript's
own argument, `paper/sections/02-preliminaries.tex:152`. -/
theorem exists_quiet_of_compactPositiveTimeSupport {f : VelocityField}
    (hf : CompactPositiveTimeSupport f) :
    ∃ τ : ℝ, 0 < τ ∧ τ < 1 ∧ ∀ t : ℝ, t ≤ τ → ∀ x : Space, f (t, x) = 0 := by
  rcases (tsupport f).eq_empty_or_nonempty with hE | hne
  · refine ⟨1 / 2, by norm_num, by norm_num, fun t _ x => ?_⟩
    refine image_eq_zero_of_notMem_tsupport ?_
    rw [hE]
    exact notMem_empty _
  · obtain ⟨z, hzS, hmin⟩ := hf.1.isCompact.exists_isMinOn hne continuous_fst.continuousOn
    have hz : 0 < z.1 := (hf.2 hzS).1
    refine ⟨min (z.1 / 2) (1 / 2), lt_min (by linarith) (by norm_num),
      lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
    intro t ht x
    refine image_eq_zero_of_notMem_tsupport ?_
    intro hmem
    have hle : z.1 ≤ t := hmin hmem
    have h2 : t ≤ z.1 / 2 := ht.trans (min_le_left _ _)
    linarith

/-- The closed initial interval of Lemma 2.2 for the selected packet: `F`, `U`
and `P` all vanish on `[0,τ]` with `0 < τ < 1`.  The force part is the
manuscript's compactness argument above; the velocity and pressure parts are
the early vanishing already carried by
`NSFormalization.Source.selected_packet_every_viscosity`, so the quiet length
is the smaller of the two. -/
theorem exists_packet_quiet {ν : ℝ} {u f : VelocityField} {p : PressureField}
    {K : Set Space} (hprop : CandidateProperties ν u p f K)
    (hearly : ∀ t : ℝ, |t| ≤ 3 / 8 → ∀ x : Space, u (t, x) = 0 ∧ p (t, x) = 0) :
    ∃ τ : ℝ, 0 < τ ∧ τ < 1 ∧
      (∀ t ∈ Icc (0 : ℝ) τ, ∀ x : Space, f (t, x) = 0) ∧
      (∀ t ∈ Icc (0 : ℝ) τ, ∀ x : Space, u (t, x) = 0) ∧
      (∀ t ∈ Icc (0 : ℝ) τ, ∀ x : Space, p (t, x) = 0) := by
  obtain ⟨σ, hσ, _, hfq⟩ := exists_quiet_of_compactPositiveTimeSupport hprop.force_support
  have habs : ∀ t ∈ Icc (0 : ℝ) (min σ (3 / 8)), |t| ≤ 3 / 8 := by
    intro t ht
    rw [abs_of_nonneg ht.1]
    exact ht.2.trans (min_le_right _ _)
  refine ⟨min σ (3 / 8), lt_min hσ (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_, ?_, ?_⟩
  · exact fun t ht x => hfq t (ht.2.trans (min_le_left _ _)) x
  · exact fun t ht x => (hearly t (habs t ht) x).1
  · exact fun t ht x => (hearly t (habs t ht) x).2

end NSFormalization.Section4.I01
