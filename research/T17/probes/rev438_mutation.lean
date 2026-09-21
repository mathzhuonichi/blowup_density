import NSFormalization.Section3.T17.Sobolev

/-!
Reviewer negative probe for lane 438.

This deliberately widens the main theorem's Sobolev-order interval from
`s ≤ 1` to `s ≤ 2`.  The `exact` below must fail because the delivered theorem
only proves the paper's range `0 ≤ s ≤ 1`.
-/

noncomputable section

namespace NSFormalization.Section3.T17.ReviewMutation

open Set MeasureTheory Metric
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 (IsPeriodicOn forceSobolevENormT)
open NSFormalization.Section3.T16
open NSFormalization.Section3.T17
open NSFormalization.Section4.A02 (SpaceTimeField)
open scoped ContDiff ENNReal Topology

theorem widened_sobolev_range (nu : ℝ) {v : SpaceTimeField}
    (hv : ContDiff ℝ ∞ v) (x0 : Space) (T delta r : ℝ)
    (hvper : IsPeriodicOn univ v)
    {theta : Space → ℝ} {eta : ℝ → ℝ}
    (O : Set Space) (thetaR eps0 : ℝ)
    (htheta : ContDiff ℝ ∞ theta) (heta : ContDiff ℝ ∞ eta)
    (hthetac : HasCompactSupport theta) (hetac : HasCompactSupport eta)
    (hthetasupp : tsupport theta ⊆ ball (0 : Space) thetaR)
    (hetasupp : tsupport eta ⊆ Ioo (-2 : ℝ) 2)
    (hr2 : r < 1 / 2) (heps0 : eps0 ≤ 1)
    (hepstime : ∀ eps ∈ Ioc (0 : ℝ) eps0, 2 * eps ^ 2 < min T delta)
    (hepsspace : ∀ eps ∈ Ioc (0 : ℝ) eps0, eps * thetaR < r) :
    ∀ s : ℝ, 0 ≤ s → s ≤ 2 →
      ∀ eps ∈ Ioc (0 : ℝ) (correctionData v x0 T theta eta O thetaR eps0).ε₀,
        forceSobolevENormT 1 s
            (correctionForce nu v (correctionData v x0 T theta eta O thetaR eps0) eps) ≤
          ENNReal.ofReal
            (sobolevConst nu hv x0 T htheta heta hthetac hetac s *
              (eps ^ ((3 : ℝ) / 2) + eps ^ ((3 : ℝ) / 2 - s))) := by
  exact force_sobolev_bound nu hv x0 T delta r hvper O thetaR eps0 htheta heta
    hthetac hetac hthetasupp hetasupp hr2 heps0 hepstime hepsspace

end NSFormalization.Section3.T17.ReviewMutation
