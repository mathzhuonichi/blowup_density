import NSFormalization.Section3.T18.Lifespan
import Bindings.MultipleRegionsV2
import NSFormalization.Section3.T24.MultipleOmegaAssembly

/-! Concrete non-vacuity of the registered `T04.multiple_regions` contract:
one quarter-ball at the centre of the fundamental cube, terminal time one,
and the registered blow-up packet at viscosity one. -/
noncomputable section
namespace MultipleOmegaNonvacuity

open Set
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.TorusData
open scoped Topology

def centre : Space := WithLp.toLp 2 (fun _ : Fin 3 ↦ (1 / 2 : ℝ))

def centres : Fin 1 → Space := fun _ ↦ centre

def radii : Fin 1 → ℝ := fun _ ↦ 1 / 4

theorem radius_pos : ∀ j : Fin 1, 0 < radii j := by
  intro j
  norm_num [radii]

theorem region_interior : ∀ j : Fin 1,
    closure (Metric.ball (centres j) (radii j)) ⊆ interior fundamentalCube := by
  intro j
  refine Metric.closure_ball_subset_closedBall.trans ?_
  rw [BlowupDensity.Bindings.fundamentalCube_eq,
    NSFormalization.Section3.T13.interior_fundamentalCube]
  intro x hx i
  have hd : ‖x - centre‖ ≤ 1 / 4 := by
    simpa only [centres, radii, Metric.mem_closedBall, dist_eq_norm] using hx
  have hc := NSFormalization.Section3.T13.abs_spaceCoord_le_norm (x - centre) i
  have hcoord : (x - centre) i = x i - 1 / 2 := rfl
  rw [hcoord] at hc
  have h := abs_le.mp (hc.trans hd)
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem regions_disjoint : Pairwise (fun i j : Fin 1 ↦
    Disjoint (Metric.ball (centres i) (radii i))
      (Metric.ball (centres j) (radii j))) := by
  intro i j hij
  exact (hij (Subsingleton.elim i j)).elim

def packet : PacketImportAPI 1 :=
  BlowupDensity.Bindings.packetImportFamily.select 1 one_pos

def unitBox : Set Space := interior fundamentalCube

theorem unitBox_domain : NSFormalization.Section3.T23.IsBoundedBoxOrSmoothDomain unitBox := by
  refine ⟨isOpen_interior, ?_, ?_, Or.inl ?_⟩
  · exact NSFormalization.Section3.T18.isCompact_fundamentalCube.isBounded.subset interior_subset
  · exact ⟨centre, region_interior 0 (subset_closure (Metric.mem_ball_self (radius_pos 0)))⟩
  · refine ⟨fun _ => 0, fun _ => 1, fun _ => zero_lt_one, ?_⟩
    exact NSFormalization.Section3.T13.interior_fundamentalCube

def data : NSFormalization.Section3.T24.RegionsOmegaData 1 packet.velocity
    packet.pressure packet.force packet.carrier packet.energyBound packet.dissipationBound where
  packet :=
    { extension_smooth := packet.velocity_extension_smooth
      carrier_compact := packet.carrier_compact
      support := packet.velocity_support
      square_int := packet.square_integrable
      zero_initial := packet.zero_initial_velocity
      energy_isLUB := packet.energy_isLUB
      dissipation_int := packet.dissipation_integrable
      dissipation_eq := packet.dissipation_eq }
  pressure_support := packet.pressure_support
  pressure_smooth := packet.pressure_extension_smooth
  force_smooth := packet.force_smooth
  force_support := packet.force_support
  force_zero := packet.force_zero_nonpos
  momentum := packet.extension_navier_stokes
  divergence := packet.extension_divergence_free
  blowup := packet.speed_unbounded
  Ω := unitBox
  hΩ := unitBox_domain
  T := 1
  hT := one_pos
  N := 1
  N_pos := one_pos
  regionCenter := centres
  regionRadius := radii
  regionRadius_pos := radius_pos
  region_interior := region_interior
  regions_disjoint := regions_disjoint

def api := NSFormalization.Section3.T24.multipleRegionsOmegaAPI data

theorem region_blowup_zero :
    NSFormalization.Section3.T24.SpeedUnboundedAtOn 1
      (Metric.ball (centres 0) (radii 0)) api.assembled_velocity :=
  api.region_blowup (⟨0, by decide⟩ : Fin 1)

theorem no_slip : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x ∈ frontier unitBox,
    api.assembled_velocity (t, x) = 0 := api.no_slip

/-- The registered V2 constructor supplies the same concrete geometry. -/
def registeredAPI := BlowupDensity.Bindings.MultipleRegionsV2.multipleRegionsOmega
  packet unitBox unitBox_domain 1 one_pos 1 one_pos centres radii
  radius_pos region_interior regions_disjoint

theorem registered_blowup_zero : SpeedUnboundedAtOn 1
    (Metric.ball (centres 0) (radii 0)) registeredAPI.assembled_velocity :=
  registeredAPI.region_blowup 0

theorem registered_no_slip : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x ∈ frontier unitBox,
    registeredAPI.assembled_velocity (t, x) = 0 := registeredAPI.no_slip

end MultipleOmegaNonvacuity
