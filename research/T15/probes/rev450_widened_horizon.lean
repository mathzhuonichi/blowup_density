import NSFormalization.Section3.T15.SobolevPath

/-!
Reviewer negative probe: the main Sobolev-path conclusion is substantively
mutated by widening `[0, T)` to `[0, T + 1)`.  The lane theorem must not close
this statement, because the packet hypotheses control only physical times
strictly below `T`.
-/

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
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀, ∀ m : ℕ, ∃ G : ℝ → PeriodicSobolev (m : ℝ),
      ContinuousOn G (Ico (0 : ℝ) (place.T + 1)) ∧
        ∀ t ∈ Ico (0 : ℝ) (place.T + 1),
          IsPeriodicDatum (m : ℝ)
            (fun x => periodizedScaledVelocity u place.x₀ place.T ε (t, x)) (G t) := by
  exact periodized_sobolev hext hK hu place

end NSFormalization.Section3.T15.ReviewerProbe
