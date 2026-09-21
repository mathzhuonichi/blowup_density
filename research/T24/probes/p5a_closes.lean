import NSFormalization.Section3.T24.MultipleOmegaComponents
noncomputable section
namespace P5aProbe
open NSFormalization.Section3.T24
open NSFormalization.Section3.T23
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T13 NSFormalization.Section3.T15
open NSFormalization.Source.PacketScaling (zeroPastField)
open NSFormalization.Section4.A02 (SpatialField)
open scoped ContDiff Topology

variable {ν : ℝ} {u f : VelocityField} {p : PressureField}
  {K : Set Space} {M E : ℝ} (d : RegionsOmegaData ν u p f K M E)

theorem placement_time : ∀ j, (d.placement j).T = d.T := by
  exact d.placement_time

theorem placement_chart : ∀ j,
    (d.placement j).chartCenter = d.regionCenter j ∧
    (d.placement j).chartRadius = d.regionRadius j := by
  exact d.placement_chart

theorem eps_admissible : ∀ j, d.ε j ∈ Ioc (0 : ℝ) (d.placement j).ε₀ := by
  exact d.eps_admissible

theorem eps_time : ∀ j, d.ε j ^ 2 < d.T := by
  exact d.eps_time

theorem component_pin : ∀ j,
    (d.component j).velocity = scaledVelocity u (d.placement j).x₀ d.T (d.ε j) ∧
    (d.component j).pressure = domainNormalizePressure d.Ω (scaledPressure p (d.placement j).x₀ d.T (d.ε j)) := by
  exact d.component_pin

theorem component_support : ∀ j, ∀ t ∈ Ico (0 : ℝ) d.T, ∀ x : Space,
    x ∉ Metric.ball (d.regionCenter j) (d.regionRadius j) → (d.component j).velocity (t, x) = 0 := by
  exact d.component_support

theorem component_force_support : ∀ j, ∀ t : ℝ, ∀ x : Space,
    x ∉ Metric.ball (d.regionCenter j) (d.regionRadius j) →
      scaledForce f (d.placement j).x₀ d.T (d.ε j) (t, x) = 0 := by
  exact d.component_force_support

end P5aProbe
