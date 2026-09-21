import NSFormalization.Section3.T23.Differences

noncomputable section

namespace NSFormalization.Section3.T23.Rev483Nonvacuity

open Set Metric
open NavierStokes.ProblemStatement

/-- The auxiliary packet radius required by the U4 supplier is derivable from
the canonical placement fields; it is not an additional analytic assumption. -/
example {u : VelocityField} {p : PressureField} {f : VelocityField}
    {K : Set Space} (place : DomainPlacementData u p f K) :
    ∃ packetRadius : ℝ, K ⊆ ball (0 : Space) packetRadius := by
  obtain ⟨R, _, hR⟩ := place.Kstar_compact.isBounded.exists_pos_norm_le
  refine ⟨R + 1, ?_⟩
  intro y hy
  rw [mem_ball, dist_zero_right]
  linarith [hR y (place.carrier_subset hy)]

/-- The scale interval used by every U4 conclusion contains its upper endpoint. -/
example {u : VelocityField} {p : PressureField} {f : VelocityField}
    {K : Set Space} (place : DomainPlacementData u p f K)
    {base cutoffRadius packetRadius : ℝ}
    (hbase : 0 < base) (hcutoff : 0 < cutoffRadius) :
    differenceThreshold place base cutoffRadius packetRadius ∈
      Ioc (0 : ℝ) (differenceThreshold place base cutoffRadius packetRadius) := by
  exact ⟨differenceThreshold_pos place hbase hcutoff, le_rfl⟩

end NSFormalization.Section3.T23.Rev483Nonvacuity
