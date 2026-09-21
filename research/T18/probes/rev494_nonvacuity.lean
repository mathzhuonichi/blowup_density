import NSFormalization.Section3.T18.ForceAmplitude

open Set Filter Topology
open scoped ENNReal

namespace Review494

open NSFormalization.Section3.T18

/-- The admissible scale interval is inhabited for every insertion API. -/
example (data : InsertionData) (A : PeriodicInsertionAPI data) :
    A.ε₀ ∈ Ioc (0 : ℝ) A.ε₀ :=
  ⟨A.eps_pos, le_rfl⟩

/-- Canonical insertion data cannot carry the zero packet force. -/
example (data : InsertionData) : data.packetForce ≠ 0 :=
  insertionData_packetForce_ne_zero data

/-- Its packet amplitude is strictly positive and finite, so `toReal` is honest. -/
example (data : InsertionData) :
    0 < ⨆ z, ‖data.packetForce z‖ₑ ∧
      (⨆ z, ‖data.packetForce z‖ₑ) < ⊤ :=
  ⟨packetForce_sup_pos (insertionData_packetForce_ne_zero data),
    insertionData_packetForce_sup_lt_top data⟩

/-- In particular, assuming `F = 0` for a canonical record is contradictory. -/
example (data : InsertionData) (hzero : data.packetForce = 0) : False :=
  insertionData_packetForce_ne_zero data hzero

end Review494
