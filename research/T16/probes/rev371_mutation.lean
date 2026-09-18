import Tests.LocalPotential

noncomputable section
namespace BlowupDensity.Review371

open Set MeasureTheory
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open scoped ContDiff

/- A substantive mutation: widen the chart-radius guard from `r < 1/2`
   to `r < 1`.  The registered theorem cannot discharge this weakened
   hypothesis, so the direct transport must fail at the second argument. -/
example :
    ∀ (v U : SpaceTimeField) (K : Set Space) (x₀ : Space) (r T δ : ℝ),
      0 < r → r < 1 → 0 < T → 0 < δ → IsCompact K →
      IsPeriodicOn univ v →
      ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ Metric.ball x₀ r) →
      (∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ Metric.ball x₀ r,
        spatialDivergence v t x = 0) →
      (∀ t ∈ Ioo (0 : ℝ) 1, tsupport (fun x => U (t, x)) ⊆ K) →
      ∃ D : CutoffData, LocalPotentialAPI v U K x₀ r T δ D := by
  intro v U K x₀ r T δ hr hr1 hT hδ hK hper hcont hdiv hUsupp
  exact Bindings.localPotential v U K x₀ r T δ hr hr1 hT hδ hK hper hcont hdiv hUsupp

end BlowupDensity.Review371
