import Tests.PacketImport

noncomputable section

namespace BlowupDensity.Review355

open Set MeasureTheory
open BlowupDensity.Contracts.V1
open BlowupDensity.Bindings

/- Substantive mutation: the contract's viscous factor `2 * ν` is changed to
   `3 * ν`.  The registered proof must no longer typecheck. -/
example (ν : ℝ) (hν : 0 < ν) :
    ∀ t ∈ Ico (0 : ℝ) 1,
      l2Sq (Bindings.packet ν hν).velocity t +
          3 * ν * (∫ s in Ioo (0 : ℝ) t,
            dissipation (Bindings.packet ν hν).velocity s)
        ≤ 2 * (∫ s in Ioo (0 : ℝ) t,
          Real.sqrt (l2Sq (Bindings.packet ν hν).force s) *
            accumulatedForce (Bindings.packet ν hν).force s) := by
  exact (Bindings.packetImportFamily.select ν hν).energy.energy_le_work

end BlowupDensity.Review355
