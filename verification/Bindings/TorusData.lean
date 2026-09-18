import Contracts.V1.TorusData
import NSFormalization.Section3.T10.PhysicalBridge
import NSFormalization.Section3.T10.DatumBasics
import NSFormalization.Section3.T10.Parseval
import NSFormalization.Section3.T10.Leray

/-!
# Binding for the periodic data contract

Every contract-side definition is checked against the canonical T10 data
layer by `rfl`.  The pointwise bridge form is used for polymorphic definitions
whose implicit type or instance arguments make an unannotated bare function
equality underconstrained.

The ten API fields are assembled directly from the named theorems in the four
canonical T10 proof modules.
-/

noncomputable section

namespace BlowupDensity.Bindings

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open scoped ENNReal BigOperators ComplexConjugate

/-! ## 1. Definitional drift guards -/

theorem periodicFrequency_eq :
    PeriodicFrequency = NSFormalization.Section3.T10.PeriodicFrequency := rfl

theorem periodicTorus_eq :
    PeriodicTorus = NSFormalization.Section3.T10.PeriodicTorus := rfl

theorem periodicTorusMeasure_eq :
    periodicTorusMeasure = NSFormalization.Section3.T10.periodicTorusMeasure := rfl

/-- Pointwise because the implicit result type `E` makes the bare polymorphic
function equality underconstrained. -/
theorem isPeriodicSpatial_eq {E : Type*} [Add E] (z : Space → E) :
    IsPeriodicSpatial z = NSFormalization.Section3.T10.IsPeriodicSpatial z := rfl

/-- Pointwise because both the implicit result type and the set argument must
be fixed before the two polymorphic predicates can be compared. -/
theorem isPeriodicOn_eq {E : Type*} (I : Set ℝ) (z : SpaceTime → E) :
    IsPeriodicOn I z = NSFormalization.Section3.T10.IsPeriodicOn I z := rfl

/-- Pointwise because a bare equality leaves the implicit codomain `E`
unconstrained. -/
theorem torusLift_eq {E : Type*} (f : Space → E) (z : PeriodicTorus) :
    torusLift f z = NSFormalization.Section3.T10.torusLift f z := rfl

theorem periodicFourierCoeff_eq (f : Space → ℂ) (k : PeriodicFrequency) :
    periodicFourierCoeff f k =
      NSFormalization.Section3.T10.periodicFourierCoeff f k := rfl

theorem periodicFrequencyWeight_eq (k : PeriodicFrequency) :
    periodicFrequencyWeight k =
      NSFormalization.Section3.T10.periodicFrequencyWeight k := rfl

theorem periodicScalarData_eq :
    PeriodicScalarData = NSFormalization.Section3.T10.PeriodicScalarData := rfl

theorem periodicVectorData_eq :
    PeriodicVectorData = NSFormalization.Section3.T10.PeriodicVectorData := rfl

theorem realPeriodicSubmodule_eq :
    realPeriodicSubmodule = NSFormalization.Section3.T10.realPeriodicSubmodule := rfl

/-- The phantom-order carrier is bridged through its defining real submodule. -/
theorem periodicSobolev_eq (s : ℝ) :
    PeriodicSobolev s = NSFormalization.Section3.T10.PeriodicSobolev s := by
  exact realPeriodicSubmodule_eq

theorem periodicSobolevDataNorm_eq (s : ℝ) (A : PeriodicSobolev s) :
    periodicSobolevDataNorm s A =
      NSFormalization.Section3.T10.periodicSobolevDataNorm s A := rfl

theorem isPeriodicDatum_eq (s : ℝ) (z : SpatialField) (A : PeriodicSobolev s) :
    IsPeriodicDatum s z A = NSFormalization.Section3.T10.IsPeriodicDatum s z A := rfl

theorem periodicSobolevENorm_eq (s : ℝ) (z : SpatialField) :
    periodicSobolevENorm s z =
      NSFormalization.Section3.T10.periodicSobolevENorm s z := rfl

theorem meanT_eq (z : SpatialField) :
    meanT z = NSFormalization.Section3.T10.meanT z := rfl

theorem constantPartT_eq (z : SpatialField) :
    constantPartT z = NSFormalization.Section3.T10.constantPartT z := rfl

theorem meanZeroPartT_eq (z : SpatialField) :
    meanZeroPartT z = NSFormalization.Section3.T10.meanZeroPartT z := rfl

theorem meanDecompositionT_eq (z : SpatialField) :
    meanDecompositionT z = NSFormalization.Section3.T10.meanDecompositionT z := rfl

theorem meanZeroPeriodicSobolev_eq (s : ℝ) :
    meanZeroPeriodicSobolev s =
      NSFormalization.Section3.T10.meanZeroPeriodicSobolev s := rfl

theorem isMeanZeroT_eq (z : SpatialField) :
    IsMeanZeroT z = NSFormalization.Section3.T10.IsMeanZeroT z := rfl

theorem periodicAngularFrequencySq_eq (k : PeriodicFrequency) :
    periodicAngularFrequencySq k =
      NSFormalization.Section3.T10.periodicAngularFrequencySq k := rfl

theorem homogeneousDatumWeight_eq (s : ℝ) (k : PeriodicFrequency) :
    homogeneousDatumWeight s k =
      NSFormalization.Section3.T10.homogeneousDatumWeight s k := rfl

theorem isPeriodicHomogeneousDatum_eq (s : ℝ) (z : SpatialField)
    (A : PeriodicSobolev s) :
    IsPeriodicHomogeneousDatum s z A =
      NSFormalization.Section3.T10.IsPeriodicHomogeneousDatum s z A := rfl

theorem periodicHomogeneousENorm_eq (s : ℝ) (z : SpatialField) :
    periodicHomogeneousENorm s z =
      NSFormalization.Section3.T10.periodicHomogeneousENorm s z := rfl

theorem periodicDerivativeSymbol_eq (j : Fin 3) (k : PeriodicFrequency) :
    periodicDerivativeSymbol j k =
      NSFormalization.Section3.T10.periodicDerivativeSymbol j k := rfl

theorem isSolenoidalPeriodicDatum_eq {s : ℝ} (A : PeriodicSobolev s) :
    IsSolenoidalPeriodicDatum A =
      NSFormalization.Section3.T10.IsSolenoidalPeriodicDatum (s := s) A := rfl

theorem periodicLeray_eq (s : ℝ) (A : PeriodicSobolev s)
    (i : Fin 3) (k : PeriodicFrequency) :
    periodicLeray s A i k = NSFormalization.Section3.T10.periodicLeray s A i k := rfl

theorem isPeriodicLerayDatum_eq {s : ℝ} (A B : PeriodicSobolev s) :
    IsPeriodicLerayDatum A B =
      NSFormalization.Section3.T10.IsPeriodicLerayDatum (s := s) A B := rfl

theorem isPeriodicReweight_eq (s t : ℝ) (A : PeriodicSobolev s)
    (B : PeriodicSobolev t) :
    IsPeriodicReweight s t A B =
      NSFormalization.Section3.T10.IsPeriodicReweight s t A B := rfl

/-! ## 2. The proved API -/

/-- The ten T10 fields, assembled directly from the four canonical proof modules. -/
theorem torusData : Contracts.V1.TorusData.TorusDataAPI := {
  datum_unique := NSFormalization.Section3.T10.datum_unique
  datum_real := NSFormalization.Section3.T10.datum_real
  parseval_forward := NSFormalization.Section3.T10.parseval_forward
  parseval_backward := NSFormalization.Section3.T10.parseval_backward
  torusLift_injective := NSFormalization.Section3.T10.torusLift_injective
  torusLift_surjective := NSFormalization.Section3.T10.torusLift_surjective
  mean_decomposition := NSFormalization.Section3.T10.mean_decomposition
  meanZero_datum := NSFormalization.Section3.T10.meanZero_datum
  leray_exists_contraction := NSFormalization.Section3.T10.leray_exists_contraction
  leray_projector := NSFormalization.Section3.T10.leray_projector
}

end BlowupDensity.Bindings
