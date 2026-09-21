import Contracts.V1.Packet
import Bindings.Packet
import NSFormalization.Source.PacketBreakdown
import TestSupport.Axioms

/-! The exact public type and its transitive trust boundary are both checked. -/

noncomputable section
namespace BlowupDensity.Tests

/-- An implementation must supply every field of the unchanged specification,
at every positive viscosity. -/
def checkedPacket : ∀ ν : ℝ, 0 < ν → Contracts.V1.PacketAPI ν := Bindings.packet

run_cmd TestSupport.checkAxioms ``checkedPacket

/-- The full article statement uses one force for the construction and for
global nonexistence at every positive viscosity. -/
theorem checkedPacketBreakdown : NavierStokesR3.ProblemStatement.breakdownStatement :=
  NSFormalization.Source.source_breakdown

run_cmd TestSupport.checkAxioms ``checkedPacketBreakdown

end BlowupDensity.Tests
