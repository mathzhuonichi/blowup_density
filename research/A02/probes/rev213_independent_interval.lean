import NSFormalization.Section4.A02.MaximalWiring
namespace NSFormalization.Section4.A02
open Set
open NavierStokes.ProblemStatement (Space)
theorem rev213_independent_interval {ν T : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (w : ClassicalSolutionR ν a f T)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (fun x : Space => w.velocity (t, x)) ∈ initialClassR := by
  refine ⟨⟨D01.contDiff_slice w.velocity_smooth ht, ?_⟩, ?_⟩
  · intro m
    obtain ⟨G, _, hG⟩ := w.sobolev m
    exact ⟨G t, hG t ht⟩
  · exact w.divergence t ht


end NSFormalization.Section4.A02
