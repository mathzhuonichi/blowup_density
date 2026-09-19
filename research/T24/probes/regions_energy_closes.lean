import NSFormalization.Section3.T24.MultipleRegions

/-! The four `MultipleRegionsAPI` field types, instantiated with `RegionsData`'s
placements, components, scales and explicit assembled velocity. No assembled
solution or input energy estimate is assumed. -/
noncomputable section
namespace NSFormalization.Section3.T24.RegionsEnergyProbe
open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open scoped ENNReal
variable {ν : ℝ} {u f : VelocityField} {p : PressureField}
  {K : Set Space} {M E : ℝ} (d : RegionsData ν u p f K M E)

-- MultipleRegionsAPI.region_agreement
 theorem agreement : ∀ j, ∀ t ∈ Ico (0 : ℝ) d.T,
    ∀ x ∈ Metric.ball (d.regionCenter j) (d.regionRadius j),
      d.assembledVelocity (t, x) = (d.component j).velocity (t, x) := by
  exact d.region_agreement

-- MultipleRegionsAPI.region_blowup
 theorem blowup : ∀ j,
    SpeedUnboundedAtOn d.T (Metric.ball (d.regionCenter j) (d.regionRadius j))
      d.assembledVelocity := by
  exact d.region_blowup

-- MultipleRegionsAPI.energy_bound; its M is d's M.
 theorem energy : (energyEssSupT d.T d.assembledVelocity) ^ (2 : ℕ) ≤
    ENNReal.ofReal (M ^ 2 * ∑ j, d.ε j) := by
  exact d.energy_bound

-- MultipleRegionsAPI.dissipation_bound; its D is d's E.
 theorem dissipation : (energyGradientT d.T d.assembledVelocity) ^ (2 : ℕ) =
    ENNReal.ofReal (E ^ 2 * ∑ j, d.ε j) := by
  exact d.dissipation_bound

end NSFormalization.Section3.T24.RegionsEnergyProbe
