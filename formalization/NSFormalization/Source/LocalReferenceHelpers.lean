import NSFormalization.Paper1.TimeExtension
import NSFormalization.Source.LocalizedBlowup
import NavierStokes.PeriodicUniqueness

/-! Local extension and residual locality for a reference regular only on its time slab. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace NSFormalization.Source.LocalReferenceHelpers
open NavierStokes.ProblemStatement NSFormalization.Paper1
open LocalizedBlowup PacketScaling

/-- The actual arbitrary-viscosity residual is local in both fields. -/
theorem residual_congr {u v : VelocityField} {p q : PressureField} {z : SpaceTime}
    (ν : ℝ) (hu : u =ᶠ[𝓝 z] v) (hp : p =ᶠ[𝓝 z] q) :
    residual ν u p z.1 z.2 = residual ν v q z.1 z.2 := by
  simp only [residual, NavierStokes.ResidualRegularity.temporalDerivative_congr hu,
    NavierStokes.ResidualRegularity.advection_congr hu,
    NavierStokes.ResidualRegularity.spatialLaplacian_congr hu,
    NavierStokes.ResidualRegularity.pressureGradient_congr hp]

/-- A pressure reference has the same time-cutoff extension property as a velocity. -/
theorem pressure_truncation_smooth {q : PressureField} {I : Set ℝ} (hI : IsOpen I)
    (hq : ContDiffOn ℝ ∞ q (I ×ˢ (univ : Set Space)))
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hsupport : tsupport χ ⊆ I) :
    ContDiff ℝ ∞ (fun z : SpaceTime => χ z.1 * q z) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases ht : z.1 ∈ I
  · exact ((hχ.comp contDiff_fst).contDiffAt).mul
      ((hq z ⟨ht, mem_univ _⟩).contDiffAt ((hI.prod isOpen_univ).mem_nhds ⟨ht, mem_univ _⟩))
  · have hn : z.1 ∉ tsupport χ := fun h => ht (hsupport h)
    have hevent : ∀ᶠ p : SpaceTime in 𝓝 z, p.1 ∉ tsupport χ :=
      ((isClosed_tsupport χ).isOpen_compl.preimage continuous_fst).mem_nhds hn
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hevent] with p hp
    simp [image_eq_zero_of_notMem_tsupport hp]

/-- The original fields are only used on the open window around T. No
regularity or extension theorem at the initial boundary is required. -/
theorem exists_reference_pair_extension {v : VelocityField} {q : PressureField}
    (T d : ℝ) (hd : 0 < d)
    (hv : ContDiffOn ℝ ∞ v (Ioo (T - 2 * d) (T + 2 * d) ×ˢ (univ : Set Space)))
    (hq : ContDiffOn ℝ ∞ q (Ioo (T - 2 * d) (T + 2 * d) ×ˢ (univ : Set Space)))
    (hdiv : ∀ t ∈ Ioo (T - 2 * d) (T + 2 * d), ∀ x, spatialDivergence v t x = 0) :
    ∃ vhat : VelocityField, ∃ qhat : PressureField,
      ContDiff ℝ ∞ vhat ∧ ContDiff ℝ ∞ qhat ∧
      (∀ t x, spatialDivergence vhat t x = 0) ∧
      EqOn vhat v (Icc (T - d) (T + d) ×ˢ (univ : Set Space)) ∧
      EqOn qhat q (Icc (T - d) (T + d) ×ˢ (univ : Set Space)) := by
  obtain ⟨χ, hχ, _, hχone, hχsupport⟩ := exists_temporal_cutoff T d hd
  refine ⟨timeTruncation v χ, fun z => χ z.1 * q z,
    timeTruncation_smooth isOpen_Ioo hv hχ hχsupport,
    pressure_truncation_smooth isOpen_Ioo hq hχ hχsupport,
    timeTruncation_divergence hv hdiv hχsupport, ?_, ?_⟩
  · intro z hz
    exact timeTruncation_eq v χ (hχone hz.1) z.2
  · intro z hz
    simp only [hχone hz.1, one_mul]

/-- Equality on a time plateau is equality of germs at its interior points. -/
theorem eventuallyEq_of_time_plateau {E : Type*} {f g : SpaceTime → E}
    {T d t : ℝ} (h : EqOn f g (Icc (T - d) (T + d) ×ˢ (univ : Set Space)))
    (ht : t ∈ Ioo (T - d) (T + d)) (x : Space) : f =ᶠ[𝓝 (t, x)] g := by
  filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht, mem_univ x⟩] with z hz
  exact h ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2⟩

/-- Localized speed witnesses survive any change confined to earlier times. -/
theorem local_speed_congr_near {T d : ℝ} {K : Set Space} {u v : VelocityField}
    (hd : 0 < d) (hu : LocalSpeedUnboundedAt T K u)
    (heq : ∀ t ∈ Ioo (T - d) T, ∀ x ∈ K, v (t, x) = u (t, x)) :
    LocalSpeedUnboundedAt T K v := by
  intro M hM δ hδ
  obtain ⟨t, x, ht, hx, hlate, hbig⟩ := hu M hM (min δ d) (lt_min hδ hd)
  have htnear : T - d < t := by linarith [min_le_right δ d]
  refine ⟨t, x, ht, hx, ?_, ?_⟩
  · linarith [min_le_left δ d]
  · rwa [heq t ⟨htnear, ht.2⟩ x hx]

theorem local_speed_implies_speed {T : ℝ} {K : Set Space} {u : VelocityField}
    (hu : LocalSpeedUnboundedAt T K u) : SpeedUnboundedAt T u := by
  intro M hM δ hδ
  obtain ⟨t, x, ht, _, hlate, hbig⟩ := hu M hM δ hδ
  exact ⟨t, x, ht, hlate, hbig⟩

end NSFormalization.Source.LocalReferenceHelpers
