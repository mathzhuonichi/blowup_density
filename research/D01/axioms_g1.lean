import Contracts.V1.HomogeneousNorm
import Bindings.HomogeneousNorm
import Tests.HomogeneousNorm

/-!
# Axiom and conformance audit for D01 gap G1

Run with:
`cd verification && lake env lean ../research/D01/axioms_g1.lean`.
-/

noncomputable section

open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Section4.D01.Homogeneous (IsHomogeneousSliceDatum SpatialField)
open scoped ENNReal

namespace NSFormalization.Section4.D01

/-- A genuine consumer can bound the physical-field norm by any supplied datum. -/
example {s : ℝ} {z : SpatialField} {G : RealVectorSobolev s}
    (hG : IsHomogeneousSliceDatum s z G) :
    dotHomogeneousENorm s z ≤ ‖G‖ₑ :=
  le_of_isHomogeneousSlice hG

/-- The zero and finiteness lemmas have their advertised consumer shapes. -/
example (s : ℝ) : dotHomogeneousENorm s (0 : SpatialField) = 0 :=
  dotHomogeneousENorm_zero s

example {s : ℝ} {z : SpatialField}
    (hz : ∃ G : RealVectorSobolev s, IsHomogeneousSliceDatum s z G) :
    dotHomogeneousENorm s z ≠ ⊤ :=
  dotHomogeneousENorm_ne_top hz

#print axioms dotHomogeneousENorm
#print axioms dotHomogeneousENorm_le_of_isHomogeneousSlice
#print axioms le_of_isHomogeneousSlice
#print axioms dotHomogeneousENorm_zero
#print axioms dotHomogeneousENorm_ne_top_of_isHomogeneousSlice
#print axioms dotHomogeneousENorm_ne_top

end NSFormalization.Section4.D01

#print axioms BlowupDensity.Contracts.V1.HomogeneousNorm.dotHomogeneousENorm
#print axioms BlowupDensity.Bindings.dotHomogeneousENorm_eq
#print axioms BlowupDensity.Tests.checkedHomogeneousNorm
