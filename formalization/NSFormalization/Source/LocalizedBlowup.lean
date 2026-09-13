import NSFormalization.Source.PacketScaling

/-! Localized speed witnesses rule out a continuous continuation of the same trajectory. -/
noncomputable section
open Set
namespace NSFormalization.Source.LocalizedBlowup
open NavierStokes.ProblemStatement PacketScaling

/-- Arbitrarily late speed witnesses lie in one fixed spatial set. -/
def LocalSpeedUnboundedAt (T : ℝ) (K : Set Space) (u : VelocityField) : Prop :=
  ∀ M : ℝ, 0 < M → ∀ δ : ℝ, 0 < δ →
    ∃ t : ℝ, ∃ x : Space,
      t ∈ Ioo 0 T ∧ x ∈ K ∧ T - δ < t ∧ M < ‖u (t, x)‖

/-- Exact removal transfers packet blowup witnesses inside the packet support,
even if the reference is spatially unbounded. -/
theorem inserted_local_speed {T : ℝ} {K : Set Space} {b U : VelocityField}
    (hU : SpeedUnboundedAt T U)
    (hs : ∀ t ∈ Ioo (0 : ℝ) T, tsupport (fun x => U (t, x)) ⊆ K)
    (hb : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x ∈ tsupport (fun y => U (t, y)), b (t, x) = 0) :
    LocalSpeedUnboundedAt T K (fun z => b z + U z) := by
  intro M hM δ hδ
  obtain ⟨t, x, ht, hn, hv⟩ := hU M hM δ hδ
  have hx : x ∈ tsupport (fun y => U (t, y)) := by
    apply subset_tsupport
    intro hz
    change U (t, x) = 0 at hz
    rw [hz, norm_zero] at hv
    exact (not_lt_of_ge hM.le) hv
  refine ⟨t, x, ht, hs t ht hx, hn, ?_⟩
  simpa only [hb t ht x hx, zero_add] using hv

/-- A continuous extension is bounded on a compact spacetime cylinder, which
contradicts the localized witnesses. Only equality on the existing trajectory
before T is used; no arbitrary-data uniqueness theorem is assumed. -/
theorem no_continuous_continuation {T : ℝ} {K : Set Space} {u : VelocityField}
    (hK : IsCompact K) (hu : LocalSpeedUnboundedAt T K u) :
    ¬ ∃ δ : ℝ, 0 < δ ∧ ∃ W : VelocityField,
      ContinuousOn W (Icc (T - δ) (T + δ) ×ˢ K) ∧
      (∀ t ∈ Ioo (0 : ℝ) T, T - δ < t → ∀ x ∈ K, W (t, x) = u (t, x)) := by
  rintro ⟨δ, hδ, W, hW, heq⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hW
  obtain ⟨t, x, ht, hx, hlate, hbig⟩ := hu (max C 0 + 1) (by positivity) δ hδ
  have hbound := hC (t, x) ⟨⟨hlate.le, by linarith [ht.2]⟩, hx⟩
  rw [heq t ht hlate x hx] at hbound
  linarith [le_max_left C 0]

end NSFormalization.Source.LocalizedBlowup
