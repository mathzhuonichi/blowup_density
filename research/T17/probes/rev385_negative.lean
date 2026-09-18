import NSFormalization.Section3.T17.CorrectionDeriv
namespace NSFormalization.Section3.T17
open Set MeasureTheory Metric NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T16
example {v : NSFormalization.Section4.A02.SpaceTimeField} (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T : ℝ)
    {θ : Space → ℝ} {η : ℝ → ℝ} (O : Set Space) (θR ε₀ r : ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ Metric.ball (0 : Space) θR)
    (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2) (hr2 : r < 1 / 2) (hε₀ : ε₀ ≤ 1)
    (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r) :
    ∀ j m : ℕ, ∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀,
      ∀ z : SpaceTime, ∀ u : Fin m → Space, (∀ i, ‖u i‖ ≤ 1) →
      ‖iteratedFDeriv ℝ (j+m) ((correctionData v x₀ T θ η O θR ε₀).correction ε) z
        (Fin.append (fun _ : Fin j => ((1 : ℝ), (0 : Space))) (fun i => ((0 : ℝ), u i)))‖ ≤
      correctionDerivConst hv x₀ T hθ hη hθc hηc j m * (ε⁻¹) ^ (2*j+m+1) := by
  exact correction_derivative_bound hv x₀ T O θR ε₀ r hθ hη hθc hηc hθsupp hηsupp hr2 hε₀ hεspace
end NSFormalization.Section3.T17
