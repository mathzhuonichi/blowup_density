import NSFormalization.Section3.T15.SobolevPath

/-! Reviewer non-vacuity probe: admissible scales and slab times are inhabited,
and the theorem supplies an actual Fourier datum at `t = 0` for every order. -/

noncomputable section
namespace NSFormalization.Section3.T15.ReviewerProbe

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T13
open NSFormalization.Source NSFormalization.Source.PacketScaling
open scoped ContDiff

example
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hext : ContDiffOn ℝ ∞ (zeroPastField u) (Iio (1 : ℝ) ×ˢ (univ : Set Space)))
    (hK : IsCompact K)
    (hu : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space => u (t, x)) ⊆ K)
    (place : PlacementData u p f K) :
    ∃ ε ∈ Ioc (0 : ℝ) place.ε₀, ∀ m : ℕ, ∃ A : PeriodicSobolev (m : ℝ),
      IsPeriodicDatum (m : ℝ)
        (fun x => periodizedScaledVelocity u place.x₀ place.T ε (0, x)) A := by
  refine ⟨place.ε₀, ⟨place.eps_pos, le_rfl⟩, ?_⟩
  intro m
  obtain ⟨G, _, hG⟩ := periodized_sobolev hext hK hu place place.ε₀
    ⟨place.eps_pos, le_rfl⟩ m
  exact ⟨G 0, hG 0 ⟨le_rfl, place.time_pos⟩⟩

end NSFormalization.Section3.T15.ReviewerProbe
