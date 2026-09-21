import Contracts.V1.ForceAmplitude
import Bindings.PeriodicInsertion
import NSFormalization.Section3.T18.ForceAmplitude
import NSFormalization.Section3.T19.ForceAmplitude

noncomputable section
namespace BlowupDensity.Bindings
open Set Filter Topology
open Contracts.V1 Contracts.V1.Data Contracts.V1.TorusData Contracts.V1.TorusLocalTheory
open scoped ENNReal

/-- The registered packet clauses discharge every raw energy hypothesis. -/
theorem packetForce_ne_zero {ν : ℝ} (hν : 0 < ν) (P : PacketImportAPI ν) : P.force ≠ 0 :=
  NSFormalization.Section3.T18.packetForce_ne_zero hν P.carrier_compact
    P.velocity_smooth P.pressure_smooth P.force_smooth P.force_support P.velocity_support
    P.zero_initial_velocity P.divergence_free P.navier_stokes P.speed_unbounded

/-- Remark 3.13 for every registered insertion record, using its actual force. -/
theorem forceAmplitude : forceAmplitudeStatement := by
  intro ν hν P place scaling a g r δ D reference correction A
  let data := PeriodicInsertion.ofSpecInputs P place scaling a g r δ D reference correction
    A.delta_pos A.reference_force_mem A.initial_mem
  let B := PeriodicInsertion.ofSpecAPI P place scaling a g r δ D reference correction
    A.delta_pos A.reference_force_mem A.initial_mem A
  have hf := packetForce_ne_zero hν P
  refine ⟨hf, NSFormalization.Section3.T18.packetForce_sup_pos hf,
    NSFormalization.Section3.T18.packetForce_sup_lt_top P.force_smooth.continuous P.force_support.1,
    ?_, ?_, ?_⟩
  · exact fun ε hε => NSFormalization.Section3.T18.forceAmplitude_lower data B hε
  · exact NSFormalization.Section3.T18.forceAmplitude_diverges_of_ne_zero data B hf
  · exact NSFormalization.Section3.T18.forceAmplitude_real_diverges data B

/-- The selected packet used in the raw-data construction is nonzero by energy. -/
theorem selectedPacketForce_ne_zero {ν : ℝ} (hν : 0 < ν) :
    (packetImportFamily.select ν hν).force ≠ 0 :=
  packetForce_ne_zero hν _

/-- The fixed-ball family assembled from an arbitrary regular reference has
force-amplitude divergence as well as its registered norm convergence. -/
theorem forceAmplitude_from_data {ν T δ : ℝ} (hν : 0 < ν)
    {a : NSFormalization.Section4.A02.SpatialField}
    {g : NSFormalization.Section4.A02.SpaceTimeField}
    (ha : a ∈ NSFormalization.Section3.T10.initialClassT)
    (hg : g ∈ NSFormalization.Section3.T10.forceClassT) (hT : 0 < T) (hδ : 0 < δ)
    (reference : NSFormalization.Section3.T10.ClassicalSolutionT ν a g (T + δ)) :
    Tendsto (fun ε : ℝ => ⨆ z,
      ‖(NSFormalization.Section3.T19.insertion hν ha hg hT hδ reference).force ε z - g z‖ₑ)
      (𝓝[>] (0 : ℝ)) (𝓝 ⊤) :=
  NSFormalization.Section3.T19.forceAmplitude_diverges hν ha hg hT hδ reference

end BlowupDensity.Bindings
