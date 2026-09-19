import NSFormalization.Section3.T23.Boundary

/-! T23 U8: interior packet witnesses and local essential-supremum blow-up. -/

noncomputable section
namespace NSFormalization.Section3.T23
open Set MeasureTheory Filter
open NavierStokes.ProblemStatement
open NSFormalization.Source.PacketScaling
open NSFormalization.Section3.T15 (scaledVelocity scaledVelocity_eq_parabolicVelocity)
open scoped Topology

/-- The I03 rescaling argument, before spatial periodization. -/
theorem scaledPacket_speedUnbounded {U : VelocityField} (hspeed : SpeedUnboundedAtOne U)
    {T ε : ℝ} (hε : 0 < ε) (htime : ε ^ 2 ≤ T) (x₀ : Space) :
    SpeedUnboundedAt T (scaledVelocity U x₀ T ε) := by
  have hinv : (((ε⁻¹ : ℝ) ^ 2)⁻¹) = ε ^ 2 := by rw [inv_pow, inv_inv]
  rw [scaledVelocity_eq_parabolicVelocity, ← hinv]
  exact speed_unbounded_at_target (inv_pos.mpr hε) (by simpa [hinv] using htime)
    x₀ (zeroPastField_speed hspeed)

/-- Positive-level witnesses lie on the packet support, where U2 cancels the
background. U4 supplies the support in the prescribed ball; U3 supplies the
literal velocity formula. These inputs carry no blow-up conclusion. -/
theorem interior_blowup
    {U f v u : VelocityField} {p : PressureField} {K Ω : Set Space}
    (place : DomainPlacementData U p f K) (D : CutoffData)
    (hspeed : SpeedUnboundedAtOne U) {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) place.ε₀)
    (hball : closure (Metric.ball place.chartCenter place.chartRadius) ⊆ Ω)
    (hformula : ∀ z, u z = v z + D.correction ε z +
      scaledVelocity U place.x₀ place.T ε z)
    (hsupport : ∀ t ∈ Ioo (0 : ℝ) place.T,
      tsupport (fun x => scaledVelocity U place.x₀ place.T ε (t, x)) ⊆
        Metric.ball place.chartCenter place.chartRadius)
    (hcancel : ∀ t ∈ Ico (place.T - ε ^ 2) place.T,
      ∀ x ∈ tsupport (fun y => scaledVelocity U place.x₀ place.T ε (t, y)),
        v (t, x) + D.correction ε (t, x) = 0) :
    ∀ M : ℝ, 0 < M → ∀ δ : ℝ, 0 < δ →
      ∃ t : ℝ, ∃ x : Space, t ∈ Ioo 0 place.T ∧ place.T - δ < t ∧
        x ∈ Metric.ball place.chartCenter place.chartRadius ∧ x ∈ Ω ∧ M < ‖u (t, x)‖ := by
  have hb := scaledPacket_speedUnbounded hspeed hε.1
    (show ε ^ 2 ≤ place.T by linarith [place.eps_time ε hε, sq_nonneg ε]) place.x₀
  intro M hM δ hδ
  obtain ⟨t, x, ht, hnear, hlarge⟩ := hb M hM δ hδ
  have hne : scaledVelocity U place.x₀ place.T ε (t, x) ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hlarge
    linarith
  have hstart : place.T - ε ^ 2 < t := by
    by_contra hn
    exact hne (congrFun (packet_slice_zero U place.x₀ place.T ε t (not_lt.mp hn)) x)
  have hx := subset_tsupport (fun y => scaledVelocity U place.x₀ place.T ε (t, y)) hne
  have hxball := hsupport t ht hx
  refine ⟨t, x, ht, hnear, hxball, hball (subset_closure hxball), ?_⟩
  rw [hformula, hcancel t ⟨hstart.le, ht.2⟩ x hx, zero_add]
  exact hlarge

end NSFormalization.Section3.T23
