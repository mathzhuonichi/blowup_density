import Contracts.V1.CriticalRegularity
import Bindings.HomogeneousNorm
import Bindings.MaximalPartial
import NSFormalization.Section4.R43.Universal

/-!
# Binding for Proposition 4.3

The implementation supplies both conclusion fields with the same explicit
constant `R43.criticalConst`.  The datum and force classes and all three norms
are definitionally the registered `Contracts.V1` objects; the bridges below
record those equalities as drift guards.

The conclusion needs the one non-definitional bridge already proved by the A02
binding: `Section4/A02.ClassicalSolutionR` and `Contracts.V1.Data` define
distinct structures, so their lifespan suprema are identified by
`maximalPartial_maximalLifespanR_eq`, not by `rfl`.
-/

noncomputable section

namespace BlowupDensity.Bindings

open BlowupDensity.Contracts.V1.Data
open scoped ENNReal

section Correspondence

variable (q : ℝ≥0∞) (s : ℝ) (a : SpatialField) (f : SpaceTimeField)

/-- The contract's initial class is the A02-local restatement. -/
theorem criticalRegularity_initialClassR_eq :
    (initialClassR : Set SpatialField) =
      NSFormalization.Section4.A02.initialClassR := rfl

/-- The contract's force class is the A02-local restatement consumed by R43. -/
theorem criticalRegularity_memForceR_eq :
    MemForceR f = NSFormalization.Section4.A02.MemForceR f := rfl

/-- The registered spatial homogeneous norm is R43's implementation norm. -/
theorem criticalRegularity_dotHomogeneousENorm_eq :
    Contracts.V1.HomogeneousNorm.dotHomogeneousENorm =
      NSFormalization.Section4.D01.dotHomogeneousENorm := rfl

/-- The contract's homogeneous force norm is the implementation's datum-path
infimum with the identical body. -/
theorem criticalRegularity_forceHomogeneousENorm_eq :
    forceHomogeneousENorm q s f =
      NSFormalization.Section4.D01.Homogeneous.forceHomogeneousENorm q s f := rfl

/-- The contract's inhomogeneous `L¹` force norm is the implementation's
datum-path infimum with the identical body. -/
theorem criticalRegularity_forceSobolevENormL1_eq :
    forceSobolevENormL1 s f =
      NSFormalization.Section4.D01.forceSobolevENormL1 s f := rfl

end Correspondence

/-- Proposition 4.3 in the registered vocabulary.  The record has the data
field `c`, so the checked witness is a definition rather than a theorem. -/
def criticalRegularity :
    Contracts.V1.CriticalRegularity.CriticalRegularityAPI :=
  { c := NSFormalization.Section4.R43.criticalConst
    hc := NSFormalization.Section4.R43.criticalConst_pos
    universal := fun ν hν a ha f hf hsmall => by
      rw [← maximalPartial_maximalLifespanR_eq]
      exact NSFormalization.Section4.R43.universal_of_memForceR
        ν hν a ha f hf hsmall
    inhomogeneousAtZero := fun ν hν f hf hsmall => by
      rw [← maximalPartial_maximalLifespanR_eq]
      exact NSFormalization.Section4.R43.inhomogeneousAtZero_of_memForceR
        ν hν f hf hsmall }

end BlowupDensity.Bindings
