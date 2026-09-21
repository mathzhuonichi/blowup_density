import NSFormalization.Section3.T18.ForceAmplitude

open Set Filter Topology
open scoped ENNReal

namespace Review494

open NSFormalization.Section3.T18

/- Intentionally false mutation: the proof of the displayed lower bound cannot
be reused after replacing the leading packet exponent `ε⁻³` by `ε⁻²`. -/
example (data : InsertionData) (A : PeriodicInsertionAPI data)
    {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) A.ε₀) :
    ENNReal.ofReal ((ε⁻¹) ^ 2 * (⨆ z, ‖data.packetForce z‖ₑ).toReal -
      data.correction.forceProfileConst 0 * (ε⁻¹) ^ 2) ≤
        ⨆ z, ‖A.force ε z - data.g z‖ₑ := by
  exact forceAmplitude_lower data A hε

/- Intentionally false zero-force attempt: the divergence proof needs `F ≠ 0`
and cannot obtain it after rewriting the packet force to zero. -/
example (data : InsertionData) (A : PeriodicInsertionAPI data)
    (hzero : data.packetForce = 0) :
    Tendsto (fun ε : ℝ => ⨆ z, ‖A.force ε z - data.g z‖ₑ)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds ⊤) := by
  apply forceAmplitude_diverges_of_ne_zero data A
  simpa [hzero]

end Review494
