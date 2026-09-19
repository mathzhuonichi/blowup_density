import NSFormalization.Section3.T15.Pressure

/-!
Reviewer negative check for lane 447: mutate the main pressure gauge from
mean zero to mean one.  Applying `pressure_gauge` must fail specifically at
the changed constant.
-/

noncomputable section

namespace NSFormalization.Section3.T15

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Source.PacketScaling
open scoped ContDiff Topology

variable {u f : VelocityField} {p : PressureField} {K : Set Space}
variable (hK : IsCompact K)
variable (hp : ∀ t ∈ Ico (0 : ℝ) 1,
  tsupport (fun x : Space => p (t, x)) ⊆ K)
variable (hps : ContDiffOn ℝ ∞ (zeroPastField p)
  (Iio (1 : ℝ) ×ˢ (univ : Set Space)))
variable (place : PlacementData u p f K)

example : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀, ∀ t ∈ Ico (0 : ℝ) place.T,
    pressureMeanT
      (normalizedScaledPressure p place.x₀ place.T ε) t = 1 := by
  intro ε hε t ht
  have hzero := pressure_gauge hK hp hps place ε hε t ht
  exact hzero

end NSFormalization.Section3.T15
