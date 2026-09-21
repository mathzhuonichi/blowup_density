import NSFormalization.Section4.A04.EnstrophyInequality

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.C01

namespace NSFormalization.Section4.A04

/-- Deliberately false strengthening for review: the cubic growth is weakened to quadratic. -/
example
    {nu T : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField}
    (w : A02.ClassicalSolutionR nu a f T) (hf : A02.MemForceR f) (hnu : 0 < nu)
    (hOne : ∀ q ∈ Ioo (0 : ℝ) T,
      (D01.sobolevENorm 1 (slice w.velocity q)).toReal ^ 2 =
        l2Sq (slice w.velocity q) + (1 / (2 * Real.pi) ^ 2) * gradientSq (slice w.velocity q))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T)
    (hTwo : (D01.sobolevENorm 2 (slice w.velocity t)).toReal ^ 2 ≤
      l2Sq (slice w.velocity t) + 2 * (1 / (2 * Real.pi) ^ 2) * gradientSq (slice w.velocity t) +
        (1 / (2 * Real.pi) ^ 2) ^ 2 * laplacianSq (slice w.velocity t))
    (hGradient : eLpNorm (A05.gradTensor (slice w.velocity t)) 2 volume ≤
      ENNReal.ofReal (Real.sqrt (gradientSq (slice w.velocity t)))) :
    let kappa := 1 / (2 * Real.pi) ^ 2
    let Cnu := (2 * kappa * A05.gradientL6Const ^ (3 / 2 : ℝ)) ^ 4 /
      (kappa * nu / 2) ^ 3 / kappa ^ 3 + (1 + nu) + (1 + 2 * kappa / nu)
    deriv (fun q => (D01.sobolevENorm 1 (slice w.velocity q)).toReal ^ 2) t +
        nu * (D01.sobolevENorm 2 (slice w.velocity t)).toReal ^ 2 ≤
      Cnu * (1 + (D01.sobolevENorm 1 (slice w.velocity t)).toReal ^ 2) ^ 2 +
        Cnu * l2Sq (slice f t) := by
  exact enstrophy_differential w hf hnu hOne ht hTwo hGradient

end NSFormalization.Section4.A04
