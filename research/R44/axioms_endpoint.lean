import NSFormalization.Section4.R44.Endpoint
import Bindings.MaximalPartial

open NSFormalization.Section4
open NSFormalization.Section4.R44
open NSFormalization.Section4.A02
open Set MeasureTheory
open scoped ENNReal

#print axioms NSFormalization.Section4.R44.forceSobolevENormL2
#print axioms NSFormalization.Section4.R44.theta
#print axioms NSFormalization.Section4.R44.C₂
#print axioms NSFormalization.Section4.R44.C₃
#print axioms NSFormalization.Section4.R44.theta_pos
#print axioms NSFormalization.Section4.R44.C₂_pos
#print axioms NSFormalization.Section4.R44.C₃_pos
#print axioms NSFormalization.Section4.R44.radiusCoefficient
#print axioms NSFormalization.Section4.R44.radiusRate
#print axioms NSFormalization.Section4.R44.radius
#print axioms NSFormalization.Section4.R44.radiusCoefficient_pos
#print axioms NSFormalization.Section4.R44.radiusRate_pos
#print axioms NSFormalization.Section4.R44.radius_pos
#print axioms NSFormalization.Section4.R44.radiusCoefficient_small
#print axioms NSFormalization.Section4.R44.RCritical2Differential
#print axioms NSFormalization.Section4.R44.forceB_continuousOn
#print axioms NSFormalization.Section4.R44.force_norm_eq_path
#print axioms NSFormalization.Section4.R44.forceB_prefix_le
#print axioms NSFormalization.Section4.R44.Y_bound_of_differential
#print axioms NSFormalization.Section4.R44.velocity_dot_le_sobolev
#print axioms NSFormalization.Section4.R44.absorption_of_differential
#print axioms NSFormalization.Section4.R44.maximal_absorption_of_differential
#print axioms NSFormalization.Section4.R44.maximal_h2TimeIntegral_of_differential
#print axioms NSFormalization.Section4.R44.maximal_squaredHTwoIntegral_of_differential
#print axioms NSFormalization.Section4.R44.rcritical2_endpoint_of_differential
#print axioms NSFormalization.Section4.R44.rcritical2_endpoint
#print axioms NSFormalization.Section4.R44.zeroSol_differential

/-- Non-vacuity of the precise global inhomogeneous smallness hypothesis. -/
theorem zero_force_small (ν S : ℝ) (hν : 0 < ν) :
    forceSobolevENormL2 (-1 / 2) (0 : SpaceTimeField) < ENNReal.ofReal (radius ν S) := by
  have hz : forceSobolevENormL2 (-1 / 2) (0 : SpaceTimeField) = 0 := by
    apply le_antisymm _ bot_le
    apply iInf_le_of_le ⟨fun _ => 0, (fun _ _ => D01.isSobolevDatum_zero _),
      aestronglyMeasurable_zero⟩
    simp [D01.Homogeneous.bochnerDatumENorm]
  rw [hz]
  exact ENNReal.ofReal_pos.mpr (radius_pos hν)

example (ν T : ℝ) (hν : 0 < ν) (hT : 0 < T) :
    RCritical2Differential (A04.zeroSol ν T hν hT) A04.memForceR_zero :=
  zeroSol_differential ν T hν hT

/-- Uniqueness transports the zero derivative to every zero-force solution. -/
theorem zero_force_differential (ν : ℝ) (hν : 0 < ν) (T : ℝ)
    (w : ClassicalSolutionR ν (fun _ => 0) (0 : SpaceTimeField) T) :
    RCritical2Differential w A04.memForceR_zero := by
  have hw : ∀ t ∈ Ico (0 : ℝ) T, C01.slice w.velocity t = (0 : SpatialField) := by
    intro t ht
    funext x
    exact A02.velocity_unique_core hν w (A04.zeroSol ν T hν w.horizon_pos) t
      (by simpa only [min_self] using ht) x
  have hy : Y (0 : SpatialField) = 0 :=
    (zero_energy_terms ν T hν w.horizon_pos ⟨le_rfl, w.horizon_pos⟩).1
  have hz : Z (0 : SpatialField) = 0 :=
    (zero_energy_terms ν T hν w.horizon_pos ⟨le_rfl, w.horizon_pos⟩).2.1
  have hb : B (0 : SpatialField) = 0 := by
    erw [B, sobolevENorm_eq_of_isSobolevDatum (D01.isSobolevDatum_zero (-1 / 2))]
    simp
  refine ⟨0, fun _ _ _ => intervalIntegrable_const, ?_⟩
  intro t ht
  constructor
  · apply (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    rw [hw r ⟨hr.1.le, hr.2⟩, hy]
    norm_num
  · intro _
    rw [hw t ⟨ht.1.le, ht.2⟩, hy, hz]
    change 0 + ν * 0 ^ 2 ≤ C₂ * ν * 0 ^ 2 + C₃ * ν⁻¹ * B (0 : SpatialField) ^ 2
    rw [hb]
    simp

/-- Exercise the new endpoint theorem at zero force, with no assumed S1 proof. -/
example (ν S : ℝ) (hν : 0 < ν) (hS : 0 < S) :
    ENNReal.ofReal S < maximalLifespanR ν (fun _ => 0) (0 : SpaceTimeField) :=
  rcritical2_endpoint_of_differential ν S hν hS 0 A04.memForceR_zero
    (zero_force_differential ν hν) (zero_force_small ν S hν)

namespace EndpointConformance

/-- Spec.main's exact Data vocabulary and binders after the sole S1 input. -/
theorem main
    (differential : ∀ (ν : ℝ), 0 < ν →
      ∀ (f : SpaceTimeField) (hf : MemForceR f),
      ∀ T (w : ClassicalSolutionR ν (fun _ => 0) f T), RCritical2Differential w hf) :
    ∀ ν S : ℝ, 0 < ν → 0 < S →
      ∀ f : BlowupDensity.Contracts.V1.Data.SpaceTimeField,
        BlowupDensity.Contracts.V1.Data.MemForceR f →
        BlowupDensity.Contracts.V1.Data.forceSobolevENormL2 (-1 / 2) f <
          ENNReal.ofReal (radius ν S) →
          ENNReal.ofReal S < BlowupDensity.Contracts.V1.Data.maximalLifespanR ν (fun _ => 0) f := by
  intro ν S hν hS f hf hsmall
  rw [← BlowupDensity.Bindings.maximalPartial_maximalLifespanR_eq]
  exact rcritical2_endpoint differential ν S hν hS f hf hsmall

/-- Spec.nonDensityBallZero, consuming precisely the same radius and input. -/
theorem nonDensityBallZero
    (differential : ∀ (ν : ℝ), 0 < ν →
      ∀ (f : SpaceTimeField) (hf : MemForceR f),
      ∀ T (w : ClassicalSolutionR ν (fun _ => 0) f T), RCritical2Differential w hf) :
    ∀ ν T : ℝ, 0 < ν → 0 < T →
      ∀ f : BlowupDensity.Contracts.V1.Data.SpaceTimeField,
        BlowupDensity.Contracts.V1.Data.MemForceR f →
        BlowupDensity.Contracts.V1.Data.forceSobolevENormL2 (-1 / 2) f <
          ENNReal.ofReal (radius ν T) →
          f ∉ BlowupDensity.Contracts.V1.Data.breakdownSetRZero ν T := by
  intro ν T hν hT f hf hsmall hfBreakdown
  exact (not_le_of_gt (main differential ν T hν hT f hf hsmall)) hfBreakdown.2

example (ν S : ℝ) :
    radius ν S = radiusCoefficient * ν ^ (3 / 2 : ℝ) * Real.exp (-(radiusRate * ν * S)) := rfl

#print axioms main
#print axioms nonDensityBallZero
end EndpointConformance
#print axioms zero_force_small
#print axioms zero_force_differential
