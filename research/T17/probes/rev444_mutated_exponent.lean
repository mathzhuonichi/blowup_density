import NSFormalization.Section3.T17.Mixed

noncomputable section
namespace NSFormalization.Section3.T17.Rev444Mutation

open Set MeasureTheory Metric NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T15 NSFormalization.Section3.T16
open NSFormalization.Section3.T13 (fundamentalCube)
open NSFormalization.Section4.A02 (SpaceTimeField)
open scoped ContDiff ENNReal Topology

/-- Reviewer mutation: the requested exponent `alphaT p q + 1` is
substantively strengthened to `alphaT p q + 2`.  Reusing the delivered theorem
must fail with an exponent mismatch. -/
theorem mutated_force_mixed_bound (nu : ℝ) {v : SpaceTimeField}
    (hv : ContDiff ℝ ∞ v) (x0 : Space) (T delta r : ℝ)
    (hvper : IsPeriodicOn univ v) {theta : Space -> ℝ} {eta : ℝ -> ℝ}
    (O : Set Space) (thetaR eps0 : ℝ)
    (htheta : ContDiff ℝ ∞ theta) (heta : ContDiff ℝ ∞ eta)
    (hthetac : HasCompactSupport theta) (hetac : HasCompactSupport eta)
    (hthetasupp : tsupport theta ⊆ ball (0 : Space) thetaR)
    (hetasupp : tsupport eta ⊆ Ioo (-2 : ℝ) 2) (hr2 : r < 1 / 2)
    (hepstime : ∀ eps ∈ Ioc (0 : ℝ) eps0, 2 * eps ^ 2 < min T delta)
    (hepsspace : ∀ eps ∈ Ioc (0 : ℝ) eps0, eps * thetaR < r)
    (hcube : closure (ball x0 r) ⊆ interior fundamentalCube) (heps0 : eps0 ≤ 1) :
    ∀ (p q : ENNReal) [Fact (1 ≤ p)], 1 ≤ q ->
    ∀ eps ∈ Ioc (0 : ℝ) (correctionData v x0 T theta eta O thetaR eps0).ε₀,
      mixedLebesgueENormT q p
          (correctionForce nu v (correctionData v x0 T theta eta O thetaR eps0) eps) ≤
        ENNReal.ofReal
          (mixedConst nu hv x0 T htheta heta hthetac hetac p q * eps ^ (alphaT p q + 2)) := by
  exact force_mixed_bound nu hv x0 T delta r hvper O thetaR eps0 htheta heta hthetac hetac
    hthetasupp hetasupp hr2 hepstime hepsspace hcube heps0

end NSFormalization.Section3.T17.Rev444Mutation
