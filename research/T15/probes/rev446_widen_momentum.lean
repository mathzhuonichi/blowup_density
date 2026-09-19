import NSFormalization.Section3.T15.Equation

noncomputable section
namespace NSFormalization.Section3.T15.ReviewerMutation

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Source.PacketScaling

/- Reviewer-negative mutation: widen the momentum interval from `Ioo 0 T`
to `Ico 0 T`.  The lane theorem must not prove the added `t = 0` endpoint. -/
example
    {ν : ℝ} {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hK : IsCompact K)
    (hu : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space => u (t, x)) ⊆ K)
    (hp : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space => p (t, x)) ⊆ K)
    (hf : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (hfzero : ∀ t : ℝ, t ≤ 0 → ∀ x : Space, f (t, x) = 0)
    (heq : ∀ t : ℝ, t < 1 → ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν
        (zeroPastField u) (zeroPastField p) t x = zeroPastField f (t, x))
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀, ∀ t ∈ Ico (0 : ℝ) place.T, ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν
        (periodizedScaledVelocity u place.x₀ place.T ε)
        (normalizedScaledPressure p place.x₀ place.T ε) t x =
        periodizedScaledForce f place.x₀ place.T ε (t, x) := by
  exact periodized_momentum hK hu hp hf hfzero heq place

end NSFormalization.Section3.T15.ReviewerMutation
