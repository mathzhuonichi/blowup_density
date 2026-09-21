import Bindings.ForceAmplitude

open Filter Topology
open scoped ENNReal

example {ν : ℝ} (hν : 0 < ν) :
    0 < ⨆ z, ‖(BlowupDensity.Bindings.packetImportFamily.select ν hν).force z‖ₑ :=
  NSFormalization.Section3.T18.packetForce_sup_pos
    (BlowupDensity.Bindings.selectedPacketForce_ne_zero hν)

example : BlowupDensity.Contracts.V1.forceAmplitudeStatement :=
  BlowupDensity.Bindings.forceAmplitude

example (data : NSFormalization.Section3.T18.InsertionData)
    (A : NSFormalization.Section3.T18.PeriodicInsertionAPI data) :
    Tendsto (fun ε : ℝ => ⨆ z, ‖A.force ε z - data.g z‖ₑ)
      (𝓝[>] (0 : ℝ)) (𝓝 ⊤) :=
  NSFormalization.Section3.T18.forceAmplitude_diverges data A
