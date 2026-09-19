import NSFormalization.Section3.T18.Divergence
import NSFormalization.Source.Insertion

/-! T18 U5: the two cross-transport terms of `eq:insertion` vanish.
Before the packet starting time `t_ε = T - ε²` the periodized packet slice is
the constant zero field, because the parabolic source point has nonpositive
time and the packet carries the canonical zero extension into the past.  From
`t_ε` on, `correction_cancels` supplies an open set on which the corrected
background vanishes and which contains the packet's spatial support, which is
exactly the removal hypothesis of the Section 4 cross-advection lemma. -/

noncomputable section
namespace NSFormalization.Section3.T18
open Set Filter
open scoped ContDiff Topology
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T15
open NSFormalization.Section3.T16
open NSFormalization.Section4.A02 (SpaceTimeField SpaceTimeScalar SpatialField)

/-- The T16 spelling of the periodized packet used by `correction_cancels` is
the T15 periodized rescaled velocity threaded by `InsertionData`. -/
theorem periodicScaledPacket_eq (u : VelocityField) (x₀ : Space) (T ε : ℝ) :
    NSFormalization.Section3.T16.periodicScaledPacket u x₀ T ε =
      periodizedScaledVelocity u x₀ T ε := rfl

/-- `03-torus.tex:327`: before its starting time the periodized packet vanishes
everywhere in space, not merely at one point. -/
theorem packet_slice_zero (data : InsertionData) {ε t : ℝ}
    (ht : t ≤ data.place.T - ε ^ 2) :
    (fun y : Space ↦
        periodizedScaledVelocity data.packetVelocity data.place.x₀ data.place.T ε (t, y))
      = fun _ ↦ 0 := by
  funext y
  have hnonpos : (ε⁻¹) ^ 2 * (t - scaledStartTime data.place.T ε) ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
    unfold scaledStartTime
    linarith
  simp only [periodizedScaledVelocity, NSFormalization.Section3.T13.periodize,
    scaledVelocity, NSFormalization.Source.PacketScaling.zeroPastField, scaledSourcePoint]
  simp only [not_lt.mpr hnonpos, ite_false, smul_zero, tsum_zero]

/-- `03-torus.tex:322-328` `eq:bgzero`: both cross-advection terms of the
inserted triple vanish at every presingular time and every point. -/
theorem crossTransport_pair (data : InsertionData) {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) (ε₀ data))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) data.place.T) (x : Space) :
    spatialDerivative
        (periodizedScaledVelocity data.packetVelocity data.place.x₀ data.place.T ε) t x
        (correctedBackground data.reference.velocity data.D.correction ε (t, x)) = 0 ∧
      spatialDerivative
        (correctedBackground data.reference.velocity data.D.correction ε) t x
        (periodizedScaledVelocity data.packetVelocity data.place.x₀ data.place.T ε (t, x)) = 0 := by
  by_cases hstart : t < data.place.T - ε ^ 2
  · -- Pre-activation: the packet slice is the zero field, so both terms vanish.
    have hz := packet_slice_zero data (le_of_lt hstart)
    have hderiv :
        spatialDerivative
          (periodizedScaledVelocity data.packetVelocity data.place.x₀ data.place.T ε) t x = 0 := by
      simp only [spatialDerivative, hz]
      simp
    have hval :
        periodizedScaledVelocity data.packetVelocity data.place.x₀ data.place.T ε (t, x) = 0 :=
      congrFun hz x
    exact ⟨by rw [hderiv]; simp, by rw [hval]; exact map_zero _⟩
  · -- Active phase: `correction_cancels` removes the background near the packet.
    rw [not_lt] at hstart
    obtain ⟨O, hO, hsub, hzero⟩ :=
      data.correction.potential.correction_cancels ε (correction_range data hε) t ⟨hstart, ht.2⟩
    have hremove : ∀ y ∈ tsupport (fun z : Space ↦
        periodizedScaledVelocity data.packetVelocity data.place.x₀ data.place.T ε (t, z)),
        ∀ᶠ z in 𝓝 y,
          correctedBackground data.reference.velocity data.D.correction ε (t, z) = 0 := by
      intro y hy
      filter_upwards [hO.mem_nhds (hsub hy)] with z hz using hzero z hz
    obtain ⟨h1, h2⟩ := NSFormalization.Source.cross_advection_eq_zero
      (correctedBackground data.reference.velocity data.D.correction ε)
      (periodizedScaledVelocity data.packetVelocity data.place.x₀ data.place.T ε) t hremove x
    exact ⟨h2, h1⟩

/-- `research/T18/Spec.lean:1838`: `(b_ε·∇)U_ε = 0` on `[0,T)`. -/
theorem crossTransport_background_advects_packet (data : InsertionData) :
    ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data), ∀ t ∈ Ico (0 : ℝ) data.place.T, ∀ x : Space,
      spatialDerivative
          (periodizedScaledVelocity data.packetVelocity data.place.x₀ data.place.T ε) t x
          (correctedBackground data.reference.velocity data.D.correction ε (t, x)) = 0 :=
  fun _ hε _ ht x ↦ (crossTransport_pair data hε ht x).1

/-- `research/T18/Spec.lean:1848`: `(U_ε·∇)b_ε = 0` on `[0,T)`. -/
theorem crossTransport_packet_advects_background (data : InsertionData) :
    ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data), ∀ t ∈ Ico (0 : ℝ) data.place.T, ∀ x : Space,
      spatialDerivative
          (correctedBackground data.reference.velocity data.D.correction ε) t x
          (periodizedScaledVelocity data.packetVelocity data.place.x₀ data.place.T ε (t, x)) = 0 :=
  fun _ hε _ ht x ↦ (crossTransport_pair data hε ht x).2

end NSFormalization.Section3.T18
