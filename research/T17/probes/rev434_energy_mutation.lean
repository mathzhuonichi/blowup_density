import NSFormalization.Section3.T17.Energy

/- Reviewer-only negative probe: changing the claimed 3/2 rate to 5/2
   must not be discharged by the delivered theorem. -/
noncomputable section
namespace NSFormalization.Section3.T17.ReviewProbe

open Set MeasureTheory Metric
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13 (fundamentalCube)
open NSFormalization.Section3.T17
open NSFormalization.Section4.A02 (SpaceTimeField)
open scoped ContDiff ENNReal Topology BigOperators

example {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ} (O : Set Space)
    {θR r ε₀ : ℝ} (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR)
    (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hcube : closure (ball x₀ r) ⊆ interior fundamentalCube)
    (hε₀ : ε₀ ≤ 1)
    (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r)
    {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ)
      (correctionData v x₀ T θ η O θR ε₀).ε₀) :
    energyENormT T ((correctionData v x₀ T θ η O θR ε₀).correction ε) ≤
      ENNReal.ofReal (energyConst hv x₀ T hθ hη hθc hηc * ε ^ ((5 : ℝ) / 2)) := by
  exact correction_energy_bound hv x₀ T O hθ hη hθc hηc hθsupp hηsupp hcube hε₀ hεspace ε hε

end NSFormalization.Section3.T17.ReviewProbe
