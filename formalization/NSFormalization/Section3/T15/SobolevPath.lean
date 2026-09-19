import NSFormalization.Section3.T15.Energy
import NSFormalization.Section3.T11.Maximal

/-! # T15 U9: integer Sobolev datum paths and the normalized pressure gradient. -/

noncomputable section
namespace NSFormalization.Section3.T15

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T13
open NSFormalization.Source NSFormalization.Source.PacketScaling
open scoped ContDiff Topology

/-- A support bound needed only on a time slab suffices for smooth periodization there. -/
theorem contDiffOn_periodize_of_slice_support
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {v : SpaceTime → V} {T : ℝ}
    (hv : ContDiffOn ℝ ∞ v (Iio T ×ˢ (univ : Set Space)))
    (hs : ∀ t < T, tsupport (fun x => v (t, x)) ⊆ interior fundamentalCube) :
    ContDiffOn ℝ ∞ (NavierStokes.PeriodicLocalization.periodize v)
      (Iio T ×ˢ (univ : Set Space)) := by
  classical
  let w : SpaceTime → V := fun z => if z.1 < T then v z else 0
  have hw : NavierStokes.PeriodicLocalization.SupportedInCube 1 w := by
    intro z hz
    have ht : z.1 < T := by
      by_contra ht
      exact hz (by simp [w, ht])
    exact supportedInCube_of_tsupport_subset_interior (hs z.1 ht) z
      (by simpa [w, ht] using hz)
  have hsm : ContDiffOn ℝ ∞ w (Iio T ×ˢ (univ : Set Space)) :=
    hv.congr (fun z hz => by simp [w, show z.1 < T from hz.1])
  apply (NavierStokes.PeriodicLocalization.contDiffOn_periodize hw hsm).congr
  intro z hz
  apply tsum_congr
  intro n
  simp [NavierStokes.PeriodicLocalization.translate, w, show z.1 < T from hz.1]

/-- The periodized scaled velocity is jointly smooth strictly before the horizon. -/
theorem periodizedVelocity_contDiffOn
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hext : ContDiffOn ℝ ∞ (zeroPastField u) (Iio (1 : ℝ) ×ˢ (univ : Set Space)))
    (hK : IsCompact K)
    (hu : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space => u (t, x)) ⊆ K)
    (place : PlacementData u p f K) {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) place.ε₀) :
    ContDiffOn ℝ ∞ (periodizedScaledVelocity u place.x₀ place.T ε)
      (Iio place.T ×ˢ (univ : Set Space)) := by
  have h := dilate_smoothOn (f := zeroPastField u) ε⁻¹ (inv_pos.2 hε.1)
    (place.T - ε ^ 2) place.x₀ hext
  rw [NSFormalization.Section4.I03.parabolic_window ε place.T] at h
  exact contDiffOn_periodize_of_slice_support h (fun t ht =>
    scaledVelocity_slice_subset_cube hε hK hu place.carrier_subset place.eps_space
      place.chartBall_in_cube ht)

/-- The exact integer-order datum-path field of `ClassicalSolutionT`. -/
theorem periodized_sobolev
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hext : ContDiffOn ℝ ∞ (zeroPastField u) (Iio (1 : ℝ) ×ˢ (univ : Set Space)))
    (hK : IsCompact K)
    (hu : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space => u (t, x)) ⊆ K)
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀, ∀ m : ℕ, ∃ G : ℝ → PeriodicSobolev (m : ℝ),
      ContinuousOn G (Ico (0 : ℝ) place.T) ∧
        ∀ t ∈ Ico (0 : ℝ) place.T,
          IsPeriodicDatum (m : ℝ)
            (fun x => periodizedScaledVelocity u place.x₀ place.T ε (t, x)) (G t) := by
  classical
  intro ε hε m
  have hsm := (periodizedVelocity_contDiffOn hext hK hu place hε).mono
    (show Ico (0 : ℝ) place.T ×ˢ (univ : Set Space) ⊆ Iio place.T ×ˢ univ from
      fun _ hz => ⟨hz.1.2, hz.2⟩)
  have hex : ∀ t ∈ Ico (0 : ℝ) place.T, ∃ A : PeriodicSobolev (m : ℝ),
      IsPeriodicDatum (m : ℝ)
        (fun x => periodizedScaledVelocity u place.x₀ place.T ε (t, x)) A := by
    intro t ht
    apply NSFormalization.Section3.T11.exists_periodicDatum_smooth
    · exact hsm.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun x => ⟨ht, mem_univ x⟩)
    · exact NavierStokes.PeriodicLocalization.unitSpatialPeriodsOn_periodize
        (scaledVelocity u place.x₀ place.T ε) (Ico 0 place.T) t ht
  let G : ℝ → PeriodicSobolev (m : ℝ) := fun t =>
    if ht : t ∈ Ico (0 : ℝ) place.T then (hex t ht).choose else 0
  have hG : ∀ t ∈ Ico (0 : ℝ) place.T,
      IsPeriodicDatum (m : ℝ)
        (fun x => periodizedScaledVelocity u place.x₀ place.T ε (t, x)) (G t) := by
    intro t ht
    simpa only [G, dite_eq_left ht] using (hex t ht).choose_spec
  exact ⟨G, NSFormalization.Section3.T11.continuousOn_periodicDatum_path_of_slab m hsm G hG, hG⟩

/-- The exact pressure-gradient field, for the normalized pressure. -/
theorem periodized_pressure_gradient
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hext : ContDiffOn ℝ ∞ (zeroPastField p) (Iio (1 : ℝ) ×ˢ (univ : Set Space)))
    (hK : IsCompact K)
    (hp : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space => p (t, x)) ⊆ K)
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀, ∀ t ∈ Ico (0 : ℝ) place.T,
      MemLp (torusLift (fun x => pressureGradient
        (normalizedScaledPressure p place.x₀ place.T ε) t x)) 2 periodicTorusMeasure := by
  intro ε hε t ht
  have h := dilate_smoothOn (f := zeroPastField p) (ε⁻¹ ^ 2) (inv_pos.2 hε.1)
    (place.T - ε ^ 2) place.x₀ hext
  rw [NSFormalization.Section4.I03.parabolic_window ε place.T] at h
  have hper : ContDiffOn ℝ ∞ (periodizedScaledPressure p place.x₀ place.T ε)
      (Iio place.T ×ˢ (univ : Set Space)) :=
    contDiffOn_periodize_of_slice_support h (fun r hr =>
      scaledPressure_slice_subset_cube hε hK hp place.carrier_subset place.eps_space
        place.chartBall_in_cube hr)
  have hslice : ContDiff ℝ ∞
      (fun x => normalizedScaledPressure p place.x₀ place.T ε (t, x)) :=
    (hper.comp_contDiff (contDiff_const.prodMk contDiff_id)
      (fun x => ⟨ht.2, mem_univ x⟩)).sub
        (show ContDiff ℝ ∞ (fun _ : Space =>
          pressureMeanT (periodizedScaledPressure p place.x₀ place.T ε) t) from contDiff_const)
  exact memLp_torusLift_vector
    (NavierStokes.PeriodicUniqueness.pressureGradient_contDiff hslice).continuous 2

end NSFormalization.Section3.T15
