import NSFormalization.Section3.T24.MultipleRegions
import Bindings.PacketImport

/-! Reviewer non-vacuity checks for lane 469. -/
noncomputable section

namespace Rev469Nonvacuity

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T24
open NSFormalization.Section3.T15
open NSFormalization.Section4.A02 (SpaceTimeField)

variable {nu : ℝ} {u f : VelocityField} {p : PressureField}
  {K : Set Space} {M E : ℝ} (d : RegionsData nu u p f K M E)

/-- The registered packet at viscosity one. -/
def concretePacket : BlowupDensity.Contracts.V1.PacketImportAPI 1 :=
  BlowupDensity.Bindings.packetImportFamily.select 1 (by norm_num)

/-- A concrete one-region input bundle, using the canonical interior chart ball. -/
def concreteRegionsData : RegionsData (1 : ℝ) concretePacket.velocity
    concretePacket.pressure concretePacket.force concretePacket.carrier
    concretePacket.energyBound concretePacket.dissipationBound where
  packet := ⟨concretePacket.velocity_extension_smooth, concretePacket.carrier_compact,
    concretePacket.velocity_support, concretePacket.square_integrable,
    concretePacket.zero_initial_velocity, concretePacket.energy_isLUB,
    concretePacket.dissipation_integrable, concretePacket.dissipation_eq⟩
  pressure_support := concretePacket.pressure_support
  pressure_smooth := concretePacket.pressure_extension_smooth
  force_smooth := concretePacket.force_smooth
  force_support := concretePacket.force_support
  force_zero := concretePacket.force_zero_nonpos
  momentum := concretePacket.extension_navier_stokes
  divergence := concretePacket.extension_divergence_free
  blowup := concretePacket.speed_unbounded
  T := 1
  hT := by norm_num
  N := 1
  N_pos := by norm_num
  regionCenter := fun _ => placementCenter
  regionRadius := fun _ => 3 / 8
  regionRadius_pos := fun _ => by norm_num
  region_interior := fun _ => placement_chart_in_cube
  regions_disjoint := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim

/-- The hypotheses used by lane 469 have an actual registered-packet instance. -/
theorem concrete_regions_data_nonempty : Nonempty (RegionsData (1 : ℝ) concretePacket.velocity
    concretePacket.pressure concretePacket.force concretePacket.carrier
    concretePacket.energyBound concretePacket.dissipationBound) :=
  ⟨concreteRegionsData⟩

/-- The index family, time interval, and every selected region are genuinely inhabited. -/
theorem domains_inhabited :
    ∃ j : Fin d.N, ∃ t : ℝ, t ∈ Ioo (0 : ℝ) d.T ∧
      ∃ x : Space, x ∈ Metric.ball (d.regionCenter j) (d.regionRadius j) := by
  let j : Fin d.N := ⟨0, d.N_pos⟩
  refine ⟨j, d.T / 2, ⟨?_, ?_⟩, d.regionCenter j, ?_⟩
  · linarith [d.hT]
  · linarith [d.hT]
  · exact Metric.mem_ball_self (d.regionRadius_pos j)

/-- The regional blow-up theorem produces an actual point in an actual region. -/
theorem blowup_has_witness :
    ∃ j : Fin d.N, ∃ t : ℝ, ∃ x : Space,
      t ∈ Ioo (0 : ℝ) d.T ∧ d.T - 1 < t ∧
        x ∈ Metric.ball (d.regionCenter j) (d.regionRadius j) ∧
          1 < ‖d.assembledVelocity (t, x)‖ := by
  let j : Fin d.N := ⟨0, d.N_pos⟩
  obtain ⟨t, x, ht, hnear, hx, hlarge⟩ := d.region_blowup j 1 (by norm_num) 1 (by norm_num)
  exact ⟨j, t, x, ht, hnear, hx, hlarge⟩

#print axioms Rev469Nonvacuity.domains_inhabited
#print axioms Rev469Nonvacuity.blowup_has_witness
#print axioms Rev469Nonvacuity.concrete_regions_data_nonempty

end Rev469Nonvacuity
