import NSFormalization.Section4.C01.EnstrophyIdentity

open Set
open NSFormalization.Section4.A02 (ClassicalSolutionR MemForceR)

namespace NSFormalization.Section4.C01

variable {ν : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField} {T : ℝ}

/- Reviewer mutation: the force pairing has the wrong (positive) sign. -/
example (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (fun s => gradientSq (slice w.velocity s))
      (2 * advectionWork (slice w.velocity t) -
        2 * ν * laplacianSq (slice w.velocity t) +
        2 * pairing (slice f t)
          (NSFormalization.Section4.A05.lap (slice w.velocity t))) t := by
  exact enstrophyIdentity_gradientSq w hf ht

end NSFormalization.Section4.C01
