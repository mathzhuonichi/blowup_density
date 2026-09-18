import NSFormalization.Section3.T17.CorrectionProfile

/- Reviewer negative probe: the main support conclusion is substantively
   mutated from Icc (-2) 2 to Icc (-3) 3.  The existing theorem must not
   close this widened-interval target by merely omitting an argument. -/

noncomputable section
namespace NSFormalization.Section3.T17.Rev370

open Set MeasureTheory
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T16 (CutoffData)
open NSFormalization.Section4.A02 (SpaceTimeField)
open scoped ContDiff Topology

example {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) (D : CutoffData)
    (hθ : ContDiff ℝ ∞ D.θ) (hη : ContDiff ℝ ∞ D.η)
    (hθsupp : tsupport D.θ ⊆ Metric.ball (0 : Space) D.θRadius)
    (hηsupp : tsupport D.η ⊆ Ioo (-2 : ℝ) 2) :
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
      tsupport (rescaledCorrectionProfile v x₀ T ε D) ⊆
        (Icc (-3 : ℝ) 3 ×ˢ Metric.closedBall (0 : Space) D.θRadius) := by
  exact correction_profile_support hv x₀ T D hθ hη hθsupp hηsupp

end NSFormalization.Section3.T17.Rev370
