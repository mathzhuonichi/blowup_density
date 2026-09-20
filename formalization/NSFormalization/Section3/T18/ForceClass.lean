import NSFormalization.Section3.T18.Insertion

/-! T18 U2: positive-time compact force classes. The correction support fits
inside a compact positive-time interval by placement.eps_time; finite unions
then combine its support with the packet and reference force supports. -/

noncomputable section
namespace NSFormalization.Section3.T18
open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T15
open NSFormalization.Section3.T17
open NSFormalization.Section4.A02 (SpaceTimeField)

theorem scaling_range (data : InsertionData) {ε : ℝ} (hε : ε ∈ Ioc 0 (ε₀ data)) :
    ε ∈ Ioc 0 data.place.ε₀ := ⟨hε.1, hε.2.trans (eps_le_scaling data)⟩

theorem correction_range (data : InsertionData) {ε : ℝ} (hε : ε ∈ Ioc 0 (ε₀ data)) :
    ε ∈ Ioc 0 data.D.ε₀ := ⟨hε.1, hε.2.trans (eps_le_cutoff data)⟩

/-- Compact positive-time support is stable under addition. -/
theorem memForceT_add {f g : SpaceTimeField} (hf : MemForceT f) (hg : MemForceT g) :
    MemForceT (fun z ↦ f z + g z) := by
  rcases hf with ⟨hfs, hfp, K, hK, hKpos, hfK⟩
  rcases hg with ⟨hgs, hgp, L, hL, hLpos, hgL⟩
  refine ⟨hfs.add hgs, ?_, K ∪ L, hK.union hL, union_subset hKpos hLpos, ?_⟩
  · intro t ht x i
    dsimp only
    rw [hfp t ht x i, hgp t ht x i]
  · intro z hz
    rcases tsupport_add f g hz with hfz | hgz
    · exact ⟨Or.inl (hfK hfz).1, mem_univ _⟩
    · exact ⟨Or.inr (hgL hgz).1, mem_univ _⟩

theorem correction_force_mem (data : InsertionData) {ε : ℝ}
    (hε : ε ∈ Ioc 0 (ε₀ data)) :
    MemForceT (correctionForce data.ν data.reference.velocity data.D ε) := by
  have hc := correction_range data hε
  have htime := data.place.eps_time ε (scaling_range data hε)
  refine ⟨data.correction.force_smooth ε hc, data.correction.force_periodic ε hc,
    Icc (data.place.T - 2 * ε ^ 2) (data.place.T + 2 * ε ^ 2), isCompact_Icc, ?_, ?_⟩
  · intro t ht
    change 0 < t
    linarith [ht.1]
  · intro z hz
    have h := data.correction.force_support ε hc hz
    exact ⟨⟨h.1.1.le, h.1.2.le⟩, mem_univ _⟩

theorem force_mem (data : InsertionData) : ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
    force data ε ∈ forceClassT := by
  intro ε hε
  exact memForceT_add (memForceT_add data.hg (correction_force_mem data hε))
    (data.scaling.force_mem ε (scaling_range data hε))

theorem forceDifference_mem (data : InsertionData) : ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
    (fun z ↦ force data ε z - data.g z) ∈ forceClassT := by
  intro ε hε
  have h := memForceT_add (correction_force_mem data hε)
    (data.scaling.force_mem ε (scaling_range data hε))
  have heq : (fun z ↦ force data ε z - data.g z) =
      (fun z ↦ correctionForce data.ν data.reference.velocity data.D ε z +
        periodizedScaledForce data.packetForce data.place.x₀ data.place.T ε z) := by
    funext z
    simp only [force]
    abel
  rw [heq]
  exact h
end NSFormalization.Section3.T18
