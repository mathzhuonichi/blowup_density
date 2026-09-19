import NSFormalization.Section3.T16.Assembly
import NSFormalization.Section3.T17.ForceVolume

noncomputable section

namespace NSFormalization.Section3.T17.ReviewerProbe

open Set MeasureTheory Metric
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 (IsPeriodicOn periodicTorusMeasure)
open NSFormalization.Section3.T16
open NSFormalization.Section4.A02 (SpaceTimeField)
open scoped ContDiff Topology ENNReal

/- The canonical field target uses the record's scalar A.spatialVolumeConst.
   This is intentionally expected to fail: the lane theorem returns
   spatialVolumeConst θR and also requires the extra hθR premise. -/
example (ν : ℝ) {u : VelocityField} {p : PressureField} {f : VelocityField} {K : Set Space}
    (place : NSFormalization.Section3.T15.PlacementData u p f K)
    {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v) (δ r : ℝ)
    (hvper : IsPeriodicOn univ v)
    {θ : Space → ℝ} {η : ℝ → ℝ}
    (O : Set Space) (θR ε₀ : ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR)
    (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hr2 : r < 1 / 2) (hθR : 0 ≤ θR)
    (hεtime : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min place.T δ)
    (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r)
    (A : CorrectionAPI ν place v r δ
      (correctionData v place.x₀ place.T θ η O θR ε₀)) :
    ∀ ε ∈ Ioc (0 : ℝ) (correctionData v place.x₀ place.T θ η O θR ε₀).ε₀,
      periodicTorusMeasure (torusSpatialSupport
          (correctionForce ν v (correctionData v place.x₀ place.T θ η O θR ε₀) ε)) ≤
        ENNReal.ofReal (A.spatialVolumeConst * ε ^ 3) := by
  exact force_spatial_volume ν hv place.x₀ place.T δ r hvper O θR ε₀ hθ hη hθc hηc
    hθsupp hηsupp hr2 hθR hεtime hεspace

end NSFormalization.Section3.T17.ReviewerProbe
