import Tests.CriticalFiniteHorizon

open BlowupDensity.Contracts.V1.Data
open scoped ENNReal

#print axioms NSFormalization.Section4.R44.theta
#print axioms NSFormalization.Section4.R44.theta_pos
#print axioms NSFormalization.Section4.R44.radiusCoefficient
#print axioms NSFormalization.Section4.R44.radiusCoefficient_pos
#print axioms NSFormalization.Section4.R44.radiusRate
#print axioms NSFormalization.Section4.R44.radiusRate_pos
#print axioms NSFormalization.Section4.R44.radius
#print axioms NSFormalization.Section4.R44.radius_pos
#print axioms NSFormalization.Section4.R44.rcritical2_endpoint_unconditional
#print axioms NSFormalization.Section4.R44.main
#print axioms NSFormalization.Section4.R44.nonDensityBallZero
#print axioms BlowupDensity.Bindings.criticalFiniteHorizon_memForceR_eq
#print axioms BlowupDensity.Bindings.criticalFiniteHorizon_forceSobolevENormL2_eq
#print axioms BlowupDensity.Bindings.criticalFiniteHorizon_radiusCoefficient_eq
#print axioms BlowupDensity.Bindings.criticalFiniteHorizon_radiusRate_eq
#print axioms BlowupDensity.Bindings.maximalPartial_maximalLifespanR_eq
#print axioms BlowupDensity.Bindings.criticalFiniteHorizon_breakdownSetRZero_iff
#print axioms BlowupDensity.Bindings.criticalFiniteHorizon
#print axioms BlowupDensity.Tests.checkedCriticalFiniteHorizon

noncomputable section
namespace CriticalFiniteHorizonContractConformance

/-- The checked record stores the implementation's explicit leading constant. -/
theorem c_value :
    BlowupDensity.Tests.checkedCriticalFiniteHorizon.c =
      NSFormalization.Section4.R44.theta / 20 := rfl

/-- The checked record stores the implementation's explicit exponential rate. -/
theorem C_value : BlowupDensity.Tests.checkedCriticalFiniteHorizon.C = 3 := rfl

/-- The named radius has exactly the formula fixed by the Spec. -/
theorem radiusFormula : ∀ ν S : ℝ,
    BlowupDensity.Tests.checkedCriticalFiniteHorizon.radius ν S =
      (NSFormalization.Section4.R44.theta / 20) * ν ^ (3 / 2 : ℝ) *
        Real.exp (-(3 * ν * S)) :=
  BlowupDensity.Tests.checkedCriticalFiniteHorizon.radiusFormula

/-- The main field in literal `Contracts.V1.Data` vocabulary. -/
theorem main :
    ∀ ν S : ℝ, 0 < ν → 0 < S →
      ∀ f : SpaceTimeField, MemForceR f →
        forceSobolevENormL2 (-1 / 2) f <
            ENNReal.ofReal
              (NSFormalization.Section4.R44.radius ν S) →
          ENNReal.ofReal S < maximalLifespanR ν (fun _ => 0) f :=
  BlowupDensity.Tests.checkedCriticalFiniteHorizon.main

/-- The non-density field in literal `Contracts.V1.Data` vocabulary. -/
theorem nonDensityBallZero :
    ∀ ν T : ℝ, 0 < ν → 0 < T →
      ∀ f : SpaceTimeField, MemForceR f →
        forceSobolevENormL2 (-1 / 2) f <
            ENNReal.ofReal
              (NSFormalization.Section4.R44.radius ν T) →
          f ∉ breakdownSetRZero ν T :=
  BlowupDensity.Tests.checkedCriticalFiniteHorizon.nonDensityBallZero

/-- The strict smallness premise is inhabited: zero force lies in every
positive-viscosity radius and the checked main field applies. -/
theorem zeroForceMain (ν S : ℝ) (hν : 0 < ν) (hS : 0 < S) :
    ENNReal.ofReal S < maximalLifespanR ν (fun _ => 0) (0 : SpaceTimeField) := by
  apply BlowupDensity.Tests.checkedCriticalFiniteHorizon.main ν S hν hS 0
    NSFormalization.Section4.A04.memForceR_zero
  exact NSFormalization.Section4.R44.zero_force_small ν S hν

#print axioms c_value
#print axioms C_value
#print axioms radiusFormula
#print axioms main
#print axioms nonDensityBallZero
#print axioms zeroForceMain

end CriticalFiniteHorizonContractConformance
