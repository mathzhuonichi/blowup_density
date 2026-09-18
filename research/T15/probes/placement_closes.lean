import NSFormalization.Section3.T15.Placement
namespace NSFormalization.Section3.T15
open Set NavierStokes.ProblemStatement
example {u : VelocityField} {x₀ : Space} {T ε : ℝ} {K : Set Space}
    (h : ∀ t, tsupport (fun x => scaledVelocity u x₀ T ε (t,x)) ⊆ (fun y => x₀ + ε • y) '' K) :
    tsupport (fun x => scaledVelocity u x₀ T ε (0,x)) ⊆ (fun y => x₀ + ε • y) '' K :=
  scaledVelocity_tsupp_subset h 0
end NSFormalization.Section3.T15
