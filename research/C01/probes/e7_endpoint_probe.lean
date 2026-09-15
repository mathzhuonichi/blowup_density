import NSFormalization.Section4.C01.EnstrophyIdentity

open Set MeasureTheory
open NSFormalization.Section4.D01 (sobolevENorm)

namespace NSFormalization.Section4.C01

open NSFormalization.Section4.A02 (ClassicalSolutionR)

example {ν : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField} {T S : ℝ}
    (w : ClassicalSolutionR ν a f T) (hS : 0 < S) (hST : S ≤ T) :
    (∫⁻ t in Ioo (0 : ℝ) S, sobolevENorm 2 (slice w.velocity t) ^ (2 : ℝ)) ≠ ⊤ := by
  exact h2TimeIntegral_strict w hS hST

#check sobolevTwoFourier
#check enstrophyIntegralBound

end NSFormalization.Section4.C01
