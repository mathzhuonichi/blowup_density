import Contracts.V1.PacketImport
import Bindings.PacketImport
import TestSupport.Axioms

/-! Public-type, specification-field conformance, non-vacuity, and
transitive-axiom checks for `T01.packet_import` V1. -/

noncomputable section

namespace BlowupDensity.Tests

open Set MeasureTheory
open BlowupDensity.Contracts.V1
open BlowupDensity.Bindings

/-- The implementation supplies the selected family and bundles it into the
existential packet-import statement for every positive viscosity. -/
theorem checkedPacketImport : Contracts.V1.packetImportStatement := by
  let family : Contracts.V1.PacketImportFamily := Bindings.packetImportFamily
  intro ν hν
  exact ⟨family.select ν hν⟩

run_cmd TestSupport.checkAxioms ``checkedPacketImport

/-- Conformance with `research/T14/Spec.lean` field `energy_le_work`, including
the exact `2ν` and `2` factors and the registered packet fields. -/
example (ν : ℝ) (hν : 0 < ν) :
    ∀ t ∈ Ico (0 : ℝ) 1,
      l2Sq (Bindings.packet ν hν).velocity t +
          2 * ν * (∫ s in Ioo (0 : ℝ) t,
            dissipation (Bindings.packet ν hν).velocity s)
        ≤ 2 * (∫ s in Ioo (0 : ℝ) t,
          Real.sqrt (l2Sq (Bindings.packet ν hν).force s) *
            accumulatedForce (Bindings.packet ν hν).force s) :=
  (Bindings.packetImportFamily.select ν hν).energy.energy_le_work

/-- Conformance with `research/T14/Spec.lean` field `work_eq_square`, retaining
the rightmost equality of the paper's chained display. -/
example (ν : ℝ) (hν : 0 < ν) :
    ∀ t ∈ Ico (0 : ℝ) 1,
      2 * (∫ s in Ioo (0 : ℝ) t,
        Real.sqrt (l2Sq (Bindings.packet ν hν).force s) *
          accumulatedForce (Bindings.packet ν hν).force s)
        = accumulatedForce (Bindings.packet ν hν).force t ^ 2 :=
  (Bindings.packetImportFamily.select ν hν).energy.work_eq_square

/-- The selected family really carries the registered packet, rather than an
unrelated witness. -/
example (ν : ℝ) (hν : 0 < ν) :
    (packetImportFamily.select ν hν).velocity =
      (Bindings.packet ν hν).velocity := rfl

end BlowupDensity.Tests
