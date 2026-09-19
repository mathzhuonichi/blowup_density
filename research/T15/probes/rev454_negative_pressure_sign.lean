import NSFormalization.Section3.T15.Solution

noncomputable section

namespace NSFormalization.Section3.T15.Review454Negative

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T13
open NSFormalization.Source.PacketScaling
open NSFormalization.Section4.A02 (SpatialField)
open scoped ContDiff Topology

variable {nu : ℝ} {u f : VelocityField} {p : PressureField} {K : Set Space}
variable (hK : IsCompact K)
variable (hu : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space => u (t, x)) ⊆ K)
variable (hp : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space => p (t, x)) ⊆ K)
variable (hf : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
variable (hf0 : ∀ t : ℝ, t ≤ 0 → ∀ x : Space, f (t, x) = 0)
variable (hus : ContDiffOn ℝ ∞ (zeroPastField u)
  (Iio (1 : ℝ) ×ˢ (univ : Set Space)))
variable (hps : ContDiffOn ℝ ∞ (zeroPastField p)
  (Iio (1 : ℝ) ×ˢ (univ : Set Space)))
variable (heq : ∀ t : ℝ, t < 1 → ∀ x : Space,
  NavierStokesR3.ProblemStatement.navierStokesResidual nu
    (zeroPastField u) (zeroPastField p) t x = zeroPastField f (t, x))
variable (hdiv : ∀ t : ℝ, t < 1 → ∀ x : Space,
  spatialDivergence (zeroPastField u) t x = 0)
variable (place : PlacementData u p f K)

-- Substantive mutation: flip the sign of the required pinned pressure field.
example : ∀ eps ∈ Ioc (0 : ℝ) place.ε₀,
    ∃ S : ClassicalSolutionT nu (0 : SpatialField)
        (periodizedScaledForce f place.x₀ place.T eps) place.T,
      S.velocity = periodizedScaledVelocity u place.x₀ place.T eps ∧
        S.pressure = -normalizedScaledPressure p place.x₀ place.T eps := by
  exact solution hK hu hp hf hf0 hus hps heq hdiv place

end NSFormalization.Section3.T15.Review454Negative
