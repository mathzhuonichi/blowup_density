import NSFormalization.Section3.T23.Boundary
import NSFormalization.Section3.T15.Placement

/-!
# T23 U4: localized differences and boundary retention

The U3 insertion formulas are accepted only as explicit hypotheses.  This
module proves the eight U4 fields from those formulas and the already proved
placement, local-correction, packet-support, and domain-geometry facts.
-/

noncomputable section

namespace NSFormalization.Section3.T23

open Set Metric
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T15
open NSFormalization.Section3.T22 (zeroExtension)
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open scoped Topology

/-- One radius strictly larger than both the correction cutoff radius and the
packet-carrier radius supplied by the scaling API. -/
def diffSupportRadius (cutoffRadius packetRadius : ℝ) : ℝ :=
  max cutoffRadius packetRadius + 1

/-- The correction cutoff radius is strictly below the common radius. -/
theorem cutoffRadius_lt_diffSupportRadius (cutoffRadius packetRadius : ℝ) :
    cutoffRadius < diffSupportRadius cutoffRadius packetRadius := by
  unfold diffSupportRadius
  linarith [le_max_left cutoffRadius packetRadius]

/-- The packet-carrier radius is strictly below the common radius. -/
theorem packetRadius_lt_diffSupportRadius (cutoffRadius packetRadius : ℝ) :
    packetRadius < diffSupportRadius cutoffRadius packetRadius := by
  unfold diffSupportRadius
  linarith [le_max_right cutoffRadius packetRadius]

/-- The API's common support radius is positive as soon as the actual cutoff
radius is positive. -/
theorem diffSupportRadius_pos {cutoffRadius packetRadius : ℝ}
    (hcutoff : 0 < cutoffRadius) :
    0 < diffSupportRadius cutoffRadius packetRadius :=
  hcutoff.trans (cutoffRadius_lt_diffSupportRadius cutoffRadius packetRadius)

/-- Shrink any already-compatible family threshold so its closed upper
endpoint still places the entire open `ε ρ` ball inside the chart ball. -/
def differenceThreshold {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K : Set Space}
    (place : DomainPlacementData u p f K) (base cutoffRadius packetRadius : ℝ) : ℝ :=
  min base (domainPlacementMargin place.chartCenter place.x₀ place.chartRadius /
    (2 * diffSupportRadius cutoffRadius packetRadius))

/-- The shrunk threshold remains positive. -/
theorem differenceThreshold_pos {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K : Set Space}
    (place : DomainPlacementData u p f K) {base cutoffRadius packetRadius : ℝ}
    (hbase : 0 < base) (hcutoff : 0 < cutoffRadius) :
    0 < differenceThreshold place base cutoffRadius packetRadius := by
  unfold differenceThreshold
  apply lt_min hbase
  exact div_pos (domainPlacementMargin_pos place.x₀_mem)
    (mul_pos (by norm_num) (diffSupportRadius_pos hcutoff))

/-- Shrinking preserves every supplier fact already valid up to `base`. -/
theorem differenceThreshold_le_base {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K : Set Space}
    (place : DomainPlacementData u p f K) (base cutoffRadius packetRadius : ℝ) :
    differenceThreshold place base cutoffRadius packetRadius ≤ base := by
  exact min_le_left _ _

/-- The `O(ε)` difference-support ball lies in the prescribed chart ball on
the shrunk range, including the closed upper endpoint. -/
theorem diffSupport_in_chart {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K : Set Space}
    (place : DomainPlacementData u p f K) (base cutoffRadius packetRadius : ℝ)
    (hcutoff : 0 < cutoffRadius) :
    ∀ ε ∈ Ioc (0 : ℝ)
        (differenceThreshold place base cutoffRadius packetRadius),
      ball place.x₀ (ε * diffSupportRadius cutoffRadius packetRadius) ⊆
        ball place.chartCenter place.chartRadius := by
  intro ε hε x hx
  have hρ : 0 < diffSupportRadius cutoffRadius packetRadius :=
    diffSupportRadius_pos hcutoff
  have hden : 0 < 2 * diffSupportRadius cutoffRadius packetRadius := by
    positivity
  have he : ε * (2 * diffSupportRadius cutoffRadius packetRadius) ≤
      domainPlacementMargin place.chartCenter place.x₀ place.chartRadius :=
    (le_div_iff₀ hden).mp
      (hε.2.trans (min_le_right _ _))
  have heρ : ε * diffSupportRadius cutoffRadius packetRadius <
      domainPlacementMargin place.chartCenter place.x₀ place.chartRadius := by
    nlinarith [mul_pos hε.1 hρ]
  have hxρ := mem_ball.mp hx
  apply mem_ball.mpr
  calc
    dist x place.chartCenter ≤ dist x place.x₀ + dist place.x₀ place.chartCenter :=
      dist_triangle _ _ _
    _ < place.chartRadius := by
      rw [domainPlacementMargin] at heρ
      linarith

end NSFormalization.Section3.T23
