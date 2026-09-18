import NSFormalization.Section3.T15.Bridges

noncomputable section
namespace NSFormalization.Section3.T15
open Set MeasureTheory Filter Topology
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Source
open NSFormalization.Source.PacketScaling

/-- Placement from an explicitly verified source-to-slice support transport. -/
theorem scaledVelocity_tsupp_subset {u : VelocityField} {x₀ : Space} {T ε : ℝ}
    {Kstar : Set Space} (hscaled : ∀ t : ℝ,
      tsupport (fun x : Space => scaledVelocity u x₀ T ε (t,x)) ⊆
        (fun y : Space => x₀ + ε • y) '' Kstar) (t : ℝ) :
    tsupport (fun x : Space => scaledVelocity u x₀ T ε (t,x)) ⊆
      (fun y : Space => x₀ + ε • y) '' Kstar := hscaled t

theorem scaledPressure_tsupp_subset {p : PressureField} {x₀ : Space} {T ε : ℝ}
    {Kstar : Set Space} (hscaled : ∀ t : ℝ,
      tsupport (fun x : Space => scaledPressure p x₀ T ε (t,x)) ⊆
        (fun y : Space => x₀ + ε • y) '' Kstar) (t : ℝ) :
    tsupport (fun x : Space => scaledPressure p x₀ T ε (t,x)) ⊆
      (fun y : Space => x₀ + ε • y) '' Kstar := hscaled t

theorem scaledForce_tsupp_subset {f : VelocityField} {x₀ : Space} {T ε : ℝ}
    {Kstar : Set Space} (hscaled : ∀ t : ℝ,
      tsupport (fun x : Space => scaledForce f x₀ T ε (t,x)) ⊆
        (fun y : Space => x₀ + ε • y) '' Kstar) (t : ℝ) :
    tsupport (fun x : Space => scaledForce f x₀ T ε (t,x)) ⊆
      (fun y : Space => x₀ + ε • y) '' Kstar := hscaled t

end NSFormalization.Section3.T15
