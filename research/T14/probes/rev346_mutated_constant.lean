import NSFormalization.Section3.T14.PacketEnergy

noncomputable section

namespace NSFormalization.Section3.T14.ReviewProbe

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NavierStokesR3.CompactEnergy
open scoped ContDiff

/- Deliberate mutation: add `1` to the square identity's right-hand side. -/
example {f : VelocityField}
    (hforce_smooth : ContDiff ℝ ∞ f)
    (hforce_support : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f) :
    ∀ t ∈ Ico (0 : ℝ) 1,
      2 * (∫ s in Ioo (0 : ℝ) t,
        Real.sqrt (l2Sq f s) * accumulatedForce f s)
      = accumulatedForce f t ^ 2 + 1 := by
  intro t ht
  simpa using (work_eq_square_of_packet hforce_smooth hforce_support t ht)

end NSFormalization.Section3.T14.ReviewProbe
