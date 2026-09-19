import NSFormalization.Section3.T23.PressureNormalization
import NavierStokes.ResidualStability

/-! The actual un-periodized triple. Supplier facts are threaded at the same
raw packet, correction, center and horizon; no replacement insertion record. -/
noncomputable section
namespace NSFormalization.Section3.T23
open Set MeasureTheory
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T15 (scaledVelocity scaledPressure scaledForce)
open scoped ContDiff

/-- Addition uses the intersection of the two genuine open neighborhoods. -/
theorem SmoothOnClosedSlab.add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Set ℝ} {Ω : Set Space} {f g : SpaceTime → E}
    (hf : SmoothOnClosedSlab I Ω f) (hg : SmoothOnClosedSlab I Ω g) :
    SmoothOnClosedSlab I Ω (fun z => f z + g z) := by
  obtain ⟨N, hN, hn, hf⟩ := hf
  obtain ⟨M, hM, hm, hg⟩ := hg
  exact ⟨N ∩ M, hN.inter hM, fun z hz => ⟨hn hz, hm hz⟩,
    (hf.mono inter_subset_left).add (hg.mono inter_subset_right)⟩

/-- Shrinking the time interval preserves the same neighborhood. -/
theorem SmoothOnClosedSlab.mono_time {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I J : Set ℝ} {Ω : Set Space} {f : SpaceTime → E}
    (hf : SmoothOnClosedSlab I Ω f) (hJI : J ⊆ I) : SmoothOnClosedSlab J Ω f := by
  obtain ⟨N, hN, hn, hf⟩ := hf
  exact ⟨N, hN, fun z hz => hn ⟨hJI hz.1, hz.2⟩, hf⟩

/-- Globally smooth summands satisfy every domain slab convention. -/
theorem smoothOnClosedSlab_of_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : SpaceTime → E} (hf : ContDiff ℝ ∞ f) (I : Set ℝ) (Ω : Set Space) :
    SmoothOnClosedSlab I Ω f := ⟨univ, isOpen_univ, subset_univ _, hf.contDiffOn⟩

/-- Compact positive temporal supports combine by finite union. -/
theorem MemForceOmega.add {Ω : Set Space} {f g : SpaceTimeField}
    (hf : MemForceOmega Ω f) (hg : MemForceOmega Ω g) :
    MemForceOmega Ω (fun z => f z + g z) := by
  obtain ⟨hfs, K, hK, hKpos, hfK⟩ := hf
  obtain ⟨hgs, L, hL, hLpos, hgL⟩ := hg
  refine ⟨fun T => (hfs T).add (hgs T), K ∪ L, hK.union hL,
    union_subset hKpos hLpos, ?_⟩
  intro z hz
  rcases tsupport_add f g hz with hz | hz
  · exact ⟨Or.inl (hfK hz).1, mem_univ _⟩
  · exact ⟨Or.inr (hgL hz).1, mem_univ _⟩

namespace InsertedTriple
variable {ν δ r : ℝ} {Ω K : Set Space} {a : SpatialField} {g : SpaceTimeField}
  {u f : VelocityField} {p : PressureField}
  (place : DomainPlacementData u p f K) (D : CutoffData)
  (reference : ClassicalSolutionOmega ν Ω a g (place.T + δ))

/-- One threshold retains placement, correction, I03, and further geometric bounds. -/
def threshold (scalingBound geometryBound : ℝ) : ℝ :=
  min (min place.ε₀ D.ε₀) (min scalingBound geometryBound)

def velocity (ε : ℝ) : VelocityField := fun z =>
  reference.velocity z + D.correction ε z + scaledVelocity u place.x₀ place.T ε z

def pressure (ε : ℝ) : SpaceTimeScalar := domainNormalizePressure Ω
  (fun z => reference.pressure z + scaledPressure p place.x₀ place.T ε z)

def force (ε : ℝ) : VelocityField := fun z =>
  g z + correctionForce ν reference.velocity D ε z + scaledForce f place.x₀ place.T ε z

theorem velocity_formula (ε : ℝ) (z : SpaceTime) :
    velocity place D reference ε z = reference.velocity z + D.correction ε z +
      scaledVelocity u place.x₀ place.T ε z := rfl

theorem pressure_formula (ε : ℝ) :
    pressure place reference ε = domainNormalizePressure Ω
      (fun z => reference.pressure z + scaledPressure p place.x₀ place.T ε z) := rfl

theorem force_formula (ε : ℝ) (z : SpaceTime) :
    force place D reference ε z = g z + correctionForce ν reference.velocity D ε z +
      scaledForce f place.x₀ place.T ε z := rfl

theorem eps_pos {s b : ℝ} (hD : 0 < D.ε₀) (hs : 0 < s) (hb : 0 < b) :
    0 < threshold place D s b := lt_min (lt_min place.eps_pos hD) (lt_min hs hb)

theorem eps_le_scaling (s b : ℝ) : threshold place D s b ≤ place.ε₀ :=
  (min_le_left _ _).trans (min_le_left _ _)

theorem eps_le_cutoff (s b : ℝ) : threshold place D s b ≤ D.ε₀ :=
  (min_le_left _ _).trans (min_le_right _ _)

theorem eps_le_supplier (s b : ℝ) : threshold place D s b ≤ s :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem eps_le_geometry (s b : ℝ) : threshold place D s b ≤ b :=
  (min_le_right _ _).trans (min_le_right _ _)

variable {place D reference}

/-- Quiet history is global, including its closed right endpoint. -/
theorem history (C : LocalCorrectionCore reference.velocity u K place.x₀ r place.T δ D)
    {ε : ℝ} (hε : ε ∈ Ioc 0 D.ε₀) {t : ℝ}
    (ht : t ≤ place.T - 2 * ε ^ 2) (x : Space) :
    velocity place D reference ε (t, x) = reference.velocity (t, x) := by
  have hw : D.correction ε (t, x) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hz => (not_lt_of_ge ht) (C.correction_support ε hε hz).1.1)
  have hU := congrFun (packet_slice_zero u place.x₀ place.T ε t
    (by nlinarith [sq_nonneg ε])) x
  simp only [velocity, hw, hU, add_zero]

/-- The initial datum follows from quiet history and the placement time bound. -/
theorem initial (C : LocalCorrectionCore reference.velocity u K place.x₀ r place.T δ D)
    {ε : ℝ} (hε : ε ∈ Ioc 0 D.ε₀) (hplace : ε ∈ Ioc 0 place.ε₀)
    {x : Space} (hx : x ∈ Ω) : velocity place D reference ε (0, x) = a x := by
  rw [history C hε (by linarith [place.eps_time ε hplace]) x]
  exact reference.initial x hx

/-- Restrict the reference horizon, then add the smooth correction and packet. -/
theorem velocity_smooth (hδ : 0 < δ)
    (C : LocalCorrectionCore reference.velocity u K place.x₀ r place.T δ D)
    {ε : ℝ} (hε : ε ∈ Ioc 0 D.ε₀)
    (hU : ContDiffOn ℝ ∞ (scaledVelocity u place.x₀ place.T ε)
      (Iio place.T ×ˢ (univ : Set Space))) :
    SmoothOnClosedSlab (Ico 0 place.T) Ω (velocity place D reference ε) := by
  exact ((reference.velocity_smooth.mono_time
    (fun t ht => ⟨ht.1, by linarith [ht.2]⟩)).add
      (smoothOnClosedSlab_of_contDiff (C.correction_smooth ε hε) _ _)).add
    ⟨_, isOpen_Iio.prod isOpen_univ, fun z hz => ⟨hz.1.2, mem_univ _⟩, hU⟩

/-- The pressure is smooth with the domain-average gauge. -/
theorem pressure_smooth (hδ : 0 < δ) (hb : Bornology.IsBounded Ω) (hm : MeasurableSet Ω)
    {ε : ℝ} (hP : ContDiffOn ℝ ∞ (scaledPressure p place.x₀ place.T ε)
      (Iio place.T ×ˢ (univ : Set Space))) :
    SmoothOnClosedSlab (Ico 0 place.T) Ω (pressure place reference ε) := by
  exact ((reference.pressure_smooth.mono_time
    (fun t ht => ⟨ht.1, by linarith [ht.2]⟩)).add
    ⟨_, isOpen_Iio.prod isOpen_univ, fun z hz => ⟨hz.1.2, mem_univ _⟩, hP⟩).domainNormalizePressure hb hm

end InsertedTriple
end NSFormalization.Section3.T23
