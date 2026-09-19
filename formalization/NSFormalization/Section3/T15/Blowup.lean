import NSFormalization.Section3.T15.SingleCopy

/-!
# T15 U6 — unbounded speed of the periodized scaled packet

The Euclidean parabolic rescaling transports the packet's source-time-one
speed blow-up to the prescribed time `place.T`.  Every resulting witness has
nonzero velocity, so the placement support theorem puts its spatial point in
the fundamental cube.  There `velocity_singleCopy` identifies the periodized
field with the Euclidean scaled field and transfers the same witness.
-/

noncomputable section

namespace NSFormalization.Section3.T15

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T13
open NSFormalization.Source.PacketScaling

/-- `03-torus.tex:123,142-143`: every admissible periodized concentration has
unbounded pointwise speed in every left neighbourhood of the prescribed
terminal time.  The hypotheses are exactly the raw packet clauses used by the
Euclidean blow-up transport and by the single-copy identification. -/
theorem unboundedSpeed
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hcarrier_compact : IsCompact K)
    (hvelocity_support : ∀ t ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space => u (t, x)) ⊆ K)
    (hspeed : SpeedUnboundedAtOne u)
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      SpeedUnboundedAt place.T
        (periodizedScaledVelocity u place.x₀ place.T ε) := by
  intro ε hε
  have hεsq : ε ^ 2 ≤ place.T := by
    have hsquare : 0 ≤ ε ^ 2 := sq_nonneg ε
    linarith [place.eps_time ε hε]
  have hinv : (((ε⁻¹ : ℝ) ^ 2)⁻¹) = ε ^ 2 := by
    rw [inv_pow, inv_inv]
  have hscaled :
      SpeedUnboundedAt place.T (scaledVelocity u place.x₀ place.T ε) := by
    rw [scaledVelocity_eq_parabolicVelocity, ← hinv]
    exact speed_unbounded_at_target (inv_pos.mpr hε.1) (by simpa [hinv] using hεsq)
      place.x₀ (zeroPastField_speed hspeed)
  intro M hM δ hδ
  obtain ⟨t, x, ht, htnear, hlarge⟩ := hscaled M hM δ hδ
  have hne : scaledVelocity u place.x₀ place.T ε (t, x) ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hlarge
    linarith
  have hxcube : x ∈ fundamentalCube :=
    interior_subset
      (scaledVelocity_slice_subset_cube hε hcarrier_compact hvelocity_support
        place.carrier_subset place.eps_space place.chartBall_in_cube ht.2
        (subset_tsupport _ hne))
  have hcopy := velocity_singleCopy hcarrier_compact hvelocity_support place
    ε hε t ht.2 x hxcube
  exact ⟨t, x, ht, htnear, by rwa [hcopy]⟩

end NSFormalization.Section3.T15
