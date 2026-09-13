import Contracts.V1.Data
import NSFormalization.Section4.D01.OrderZeroDatum

/-!
Conformance check for D01 unit P2, sub-lemma SL7a: the order-0 Plancherel seed
(`formalization/NSFormalization/Section4/D01/OrderZeroDatum.lean`).

Run with, from `verification/`:
  lake env lean ../research/D01/axioms_sl7a.lean

Every result must depend only on the standard logical axioms
`propext`, `Classical.choice`, `Quot.sound`.
-/

open MeasureTheory

-- The SL7a seed, stated in the `Contracts.V1.Data` vocabulary: the exposed datum discharges
-- `Contracts.V1.Data.IsSobolevDatum 0 z A` for a bare `MemLp` field (defeq bridge).
example {z : BlowupDensity.Contracts.V1.Data.SpatialField}
    (hz : MemLp z 2 volume) :
    BlowupDensity.Contracts.V1.Data.IsSobolevDatum 0 z
      (NSFormalization.Section4.D01.orderZeroDatum hz) :=
  NSFormalization.Section4.D01.isSobolevDatum_orderZeroDatum hz

example {z : BlowupDensity.Contracts.V1.Data.SpatialField}
    (hz : MemLp z 2 volume) :
    ∃ A : NSFormalization.Paper3.RealVectorSobolev 0,
      BlowupDensity.Contracts.V1.Data.IsSobolevDatum 0 z A :=
  NSFormalization.Section4.D01.exists_isSobolevDatum_zero_of_memLp hz

-- The exposed datum term itself (so the norm identity can be stated against it later).
#print axioms NSFormalization.Section4.D01.orderZeroDatum
#print axioms NSFormalization.Section4.D01.isSobolevDatum_orderZeroDatum
#print axioms NSFormalization.Section4.D01.exists_isSobolevDatum_zero_of_memLp
