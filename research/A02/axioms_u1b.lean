import NSFormalization.Section4.A02.Bounds
import NSFormalization.Section4.A02.Energy
import NSFormalization.Source.BoundedViscosityUniqueness

/-! Scratch shape-check for A02 unit U1b (lane 049).

Confirms that `ClassicalSolutionR.exists_velocity_bound` and
`ClassicalSolutionR.exists_gradient_bound` (this lane) together with lane 033's
`ClassicalSolutionR.uniformFiniteEnergy` discharge exactly the `heu/hev`,
`hB0/hB`, `hG0/hG` hypotheses of
`NSFormalization.Source.BoundedViscosityUniqueness.classical_uniqueness_on_Icc`.
The remaining hypotheses (smoothness, divergence, momentum, initial equality)
are the ones a caller supplies from the two solutions; they are parameters here.

`#print axioms` must be exactly `[propext, Classical.choice, Quot.sound]`. -/

open Set MeasureTheory
open NavierStokesR3 NavierStokesR3.ProblemStatement
open NavierStokes.ProblemStatement (spatialDerivative spatialDivergence)
open NSFormalization.Source
open scoped ContDiff

namespace NSFormalization.Section4.A02

theorem u1b_shapes_ok {ν T b : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (u v : ClassicalSolutionR ν a f T)
    (hbpos : 0 < b) (hb0 : 0 ≤ b) (hbT : b < T) (hν : 0 < ν)
    (hu : ContDiffOn ℝ ∞ u.velocity (Comparison.slab 0 b))
    (hv : ContDiffOn ℝ ∞ v.velocity (Comparison.slab 0 b))
    (hp : ContDiffOn ℝ ∞ u.pressure (Comparison.slab 0 b))
    (hq : ContDiffOn ℝ ∞ v.pressure (Comparison.slab 0 b))
    (hdu : ∀ t ∈ Ioo (0 : ℝ) b, ∀ x, spatialDivergence u.velocity t x = 0)
    (hdv : ∀ t ∈ Ioo (0 : ℝ) b, ∀ x, spatialDivergence v.velocity t x = 0)
    (hNS : ∀ t ∈ Ioo (0 : ℝ) b, ∀ x,
      residual ν u.velocity u.pressure t x = residual ν v.velocity v.pressure t x)
    (hzero : ∀ x, u.velocity (0, x) = v.velocity (0, x)) :
    ∀ t ∈ Icc (0 : ℝ) b, ∀ x, u.velocity (t, x) = v.velocity (t, x) := by
  obtain ⟨B, hB0, hB⟩ := u.exists_velocity_bound hb0 hbT
  obtain ⟨Gb, hG0, hG⟩ := u.exists_gradient_bound hb0 hbT
  exact NSFormalization.Source.BoundedViscosityUniqueness.classical_uniqueness_on_Icc
    hbpos hν hu hv hp hq (u.uniformFiniteEnergy hb0 hbT) (v.uniformFiniteEnergy hb0 hbT)
    hB0 hB hG0 hG hdu hdv hNS hzero

end NSFormalization.Section4.A02

#print axioms NSFormalization.Section4.A02.u1b_shapes_ok
