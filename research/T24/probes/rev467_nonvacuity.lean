import Bindings.PacketImport
import NSFormalization.Section3.T24.MultipleComponents

noncomputable section
namespace Rev467Nonvacuity

open Set
open BlowupDensity.Contracts.V1
open NSFormalization.Section3.T13 NSFormalization.Section3.T15
open NSFormalization.Section3.T24

def P : PacketImportAPI 1 :=
  BlowupDensity.Bindings.packetImportFamily.select 1 zero_lt_one

def center : Fin 1 → Space := fun _ ↦ placementCenter
def radius : Fin 1 → ℝ := fun _ ↦ 3 / 8

def data : RegionsData 1 P.velocity P.pressure P.force
    P.carrier P.energyBound P.dissipationBound where
  packet := ⟨P.velocity_extension_smooth, P.carrier_compact, P.velocity_support,
    P.square_integrable, P.zero_initial_velocity, P.energy_isLUB,
    P.dissipation_integrable, P.dissipation_eq⟩
  pressure_support := P.pressure_support
  pressure_smooth := P.pressure_extension_smooth
  force_smooth := P.force_smooth
  force_support := P.force_support
  force_zero := P.force_zero_nonpos
  momentum := P.extension_navier_stokes
  divergence := P.extension_divergence_free
  blowup := P.speed_unbounded
  T := 1
  hT := zero_lt_one
  N := 1
  N_pos := by norm_num
  regionCenter := center
  regionRadius := radius
  regionRadius_pos := by intro j; norm_num [radius]
  region_interior := by intro j; exact placement_chart_in_cube
  regions_disjoint := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim

/-- A registered packet and an actual one-ball geometry yield a positive selected
scale with strict time smallness, so the delivered interval is inhabited. -/
example : ∃ j : Fin data.N, 0 < data.ε j ∧ data.ε j ^ 2 < data.T := by
  let j : Fin data.N := ⟨0, by simp [data]⟩
  exact ⟨j, (data.eps_admissible j).1, data.eps_time j⟩

end Rev467Nonvacuity
