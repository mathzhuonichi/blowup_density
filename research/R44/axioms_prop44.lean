import NSFormalization.Section4.R44.Prop44
import Bindings.MaximalPartial

open NSFormalization.Section4
open NSFormalization.Section4.R44
open scoped ENNReal

#print axioms NSFormalization.Section4.R44.advectionJDatumPath
#print axioms NSFormalization.Section4.R44.energyAdvectionJPairing_eq
#print axioms NSFormalization.Section4.R44.energyAdvectionJPairing_path_eq
#print axioms NSFormalization.Section4.R44.thetaAbs
#print axioms NSFormalization.Section4.R44.C₂Abs
#print axioms NSFormalization.Section4.R44.C₃Abs
#print axioms NSFormalization.Section4.R44.thetaAbs_pos
#print axioms NSFormalization.Section4.R44.trilinear_theta
#print axioms NSFormalization.Section4.R44.C₂Abs_nonneg
#print axioms NSFormalization.Section4.R44.C₂Abs_pos
#print axioms NSFormalization.Section4.R44.C₃Abs_pos
#print axioms NSFormalization.Section4.R44.C₃Abs_nonneg
#print axioms NSFormalization.Section4.R44.rcritical2EnergyDerivative
#print axioms NSFormalization.Section4.R44.rcritical2EnergyDerivative_eq
#print axioms NSFormalization.Section4.R44.rcritical2EnergyDerivative_hasDerivAt
#print axioms NSFormalization.Section4.R44.young_absorption
#print axioms NSFormalization.Section4.R44.rcritical2_pointwise
#print axioms NSFormalization.Section4.R44.smoothRcritical2EnergyDerivative
#print axioms NSFormalization.Section4.R44.smoothRcritical2EnergyDerivative_continuousOn
#print axioms NSFormalization.Section4.R44.rcritical2EnergyDerivative_eq_smooth
#print axioms NSFormalization.Section4.R44.rcritical2EnergyDerivative_intervalIntegrable
#print axioms NSFormalization.Section4.R44.rcritical2_differential
#print axioms NSFormalization.Section4.R44.theta_le_thetaAbs
#print axioms NSFormalization.Section4.R44.rCritical2Differential_of_classical
#print axioms NSFormalization.Section4.R44.rcritical2Differential_of_classical
#print axioms NSFormalization.Section4.R44.rcritical2_endpoint_unconditional
#print axioms NSFormalization.Section4.R44.main
#print axioms NSFormalization.Section4.R44.nonDensityBallZero
#print axioms NSFormalization.Section4.R44.zero_force_small

namespace Prop44Conformance
open BlowupDensity.Contracts.V1

theorem main :
    ∀ ν S : ℝ, 0 < ν → 0 < S →
      ∀ f : Data.SpaceTimeField, Data.MemForceR f →
        Data.forceSobolevENormL2 (-1 / 2) f < ENNReal.ofReal (radius ν S) →
          ENNReal.ofReal S < Data.maximalLifespanR ν (fun _ => 0) f := by
  intro ν S hν hS f hf hsmall
  rw [← BlowupDensity.Bindings.maximalPartial_maximalLifespanR_eq]
  exact rcritical2_endpoint_unconditional ν S hν hS f hf hsmall

theorem nonDensityBallZero :
    ∀ ν T : ℝ, 0 < ν → 0 < T →
      ∀ f : Data.SpaceTimeField, Data.MemForceR f →
        Data.forceSobolevENormL2 (-1 / 2) f < ENNReal.ofReal (radius ν T) →
          f ∉ Data.breakdownSetRZero ν T := by
  intro ν T hν hT f hf hsmall hb
  exact (not_le_of_gt (main ν T hν hT f hf hsmall)) hb.2

theorem radiusFormula (ν S : ℝ) :
    radius ν S = radiusCoefficient * ν ^ (3 / 2 : ℝ) *
      Real.exp (-(radiusRate * ν * S)) := rfl

theorem radiusPos : ∀ ν S : ℝ, 0 < ν → 0 < S → 0 < radius ν S := by
  intro ν S hν _
  exact radius_pos hν

example (ν S : ℝ) (hν : 0 < ν) (hS : 0 < S) :
    ENNReal.ofReal S < Data.maximalLifespanR ν (fun _ => 0) (0 : Data.SpaceTimeField) :=
  main ν S hν hS 0 A04.memForceR_zero (zero_force_small ν S hν)

example (ν T : ℝ) (hν : 0 < ν) (hT : 0 < T) :
    RCritical2Differential (A04.zeroSol ν T hν hT) A04.memForceR_zero :=
  rCritical2Differential_of_classical hν A04.memForceR_zero T _

#print axioms main
#print axioms nonDensityBallZero
#print axioms radiusFormula
#print axioms radiusPos
#print axioms NSFormalization.Section4.R44.radiusCoefficient_pos
#print axioms NSFormalization.Section4.R44.radiusRate_pos
end Prop44Conformance

-- Unchanged lane 220 dependency, absent from the lane 227 base.
#print axioms NSFormalization.Section4.R44.halfHomogeneousComponent
#print axioms NSFormalization.Section4.R44.halfHomogeneousDatum
#print axioms NSFormalization.Section4.R44.halfHomogeneousDatum_norm_le
#print axioms NSFormalization.Section4.R44.halfHomogeneousDatum_isDatum
#print axioms NSFormalization.Section4.R44.inhomogeneousCriticalL3
#print axioms NSFormalization.Section4.R44.halfDatumCyclesComponent
#print axioms NSFormalization.Section4.R44.halfDatumPhysicalComponent
#print axioms NSFormalization.Section4.R44.halfDatumPhysicalComponent_real
#print axioms NSFormalization.Section4.R44.halfDatumPhysicalLp
#print axioms NSFormalization.Section4.R44.halfDatumPhysicalField
#print axioms NSFormalization.Section4.R44.halfDatumPhysicalField_memLp
#print axioms NSFormalization.Section4.R44.halfDatumPhysicalField_isDatum
#print axioms NSFormalization.Section4.R44.inhomogeneous_half_order_parseval
#print axioms NSFormalization.Section4.R44.advectionFieldJ
#print axioms NSFormalization.Section4.R44.AdvectionJDatum
#print axioms NSFormalization.Section4.R44.advectionJPairing
#print axioms NSFormalization.Section4.R44.advectionJHolder
#print axioms NSFormalization.Section4.R44.trilinearConstJ
#print axioms NSFormalization.Section4.R44.trilinearConstJ_pos
#print axioms NSFormalization.Section4.R44.advection_pairing_le_sqrt
#print axioms NSFormalization.Section4.R44.advection_pairing_le
