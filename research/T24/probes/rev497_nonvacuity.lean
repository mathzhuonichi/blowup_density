import NSFormalization.Section3.T24.MultipleOmegaAssembled
import Bindings.PacketImport

/-! Reviewer non-vacuity check for lane 497: the registered singular packet on
the open unit box, with one prescribed interior quarter-ball. -/
noncomputable section

namespace Rev497Nonvacuity

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T15
open NSFormalization.Section3.T23
open NSFormalization.Section3.T24
open NSFormalization.Section4.A02 (SpatialField)

def unitBox : Set Space :=
  {x : Space | ∀ i : Fin 3, (0 : ℝ) < x i ∧ x i < 1}

theorem unitBox_isBox : IsBoxDomain unitBox := by
  exact ⟨(fun _ ↦ 0), (fun _ ↦ 1), (fun _ ↦ zero_lt_one), rfl⟩

def center : Space := WithLp.toLp 2 (fun _ : Fin 3 ↦ (1 / 2 : ℝ))

theorem center_mem_unitBox : center ∈ unitBox := by
  intro i
  norm_num [center]

theorem unitBox_class : IsBoundedBoxOrSmoothDomain unitBox := by
  exact ⟨unitBox_isBox.open_bounded.1, unitBox_isBox.open_bounded.2,
    ⟨center, center_mem_unitBox⟩, Or.inl unitBox_isBox⟩

def centers : Fin 1 → Space := fun _ ↦ center
def radii : Fin 1 → ℝ := fun _ ↦ 1 / 4

theorem radius_pos : ∀ j : Fin 1, 0 < radii j := by
  intro j
  norm_num [radii]

theorem ball_in_unitBox : ∀ j : Fin 1,
    closure (Metric.ball (centers j) (radii j)) ⊆ unitBox := by
  intro j x hx i
  have hd : ‖x - center‖ ≤ 1 / 4 := by
    simpa only [centers, radii, Metric.mem_closedBall, dist_eq_norm] using
      (Metric.closure_ball_subset_closedBall hx)
  have hc := PiLp.norm_apply_le (x - center) i
  change |x i - center i| ≤ ‖x - center‖ at hc
  rw [show center i = (1 / 2 : ℝ) by rfl] at hc
  have h := abs_le.mp (hc.trans hd)
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem one_region_disjoint : Pairwise (fun i j : Fin 1 ↦
    Disjoint (Metric.ball (centers i) (radii i))
      (Metric.ball (centers j) (radii j))) := by
  intro i j hij
  exact (hij (Subsingleton.elim i j)).elim

def packet : BlowupDensity.Contracts.V1.PacketImportAPI 1 :=
  BlowupDensity.Bindings.packetImportFamily.select 1 one_pos

def data : RegionsOmegaData (1 : ℝ) packet.velocity packet.pressure packet.force
    packet.carrier packet.energyBound packet.dissipationBound where
  packet := ⟨packet.velocity_extension_smooth, packet.carrier_compact,
    packet.velocity_support, packet.square_integrable,
    packet.zero_initial_velocity, packet.energy_isLUB,
    packet.dissipation_integrable, packet.dissipation_eq⟩
  pressure_support := packet.pressure_support
  pressure_smooth := packet.pressure_extension_smooth
  force_smooth := packet.force_smooth
  force_support := packet.force_support
  force_zero := packet.force_zero_nonpos
  momentum := packet.extension_navier_stokes
  divergence := packet.extension_divergence_free
  blowup := packet.speed_unbounded
  Ω := unitBox
  hΩ := unitBox_class
  T := 1
  hT := one_pos
  N := 1
  N_pos := one_pos
  regionCenter := centers
  regionRadius := radii
  regionRadius_pos := radius_pos
  region_interior := ball_in_unitBox
  regions_disjoint := one_region_disjoint

/-- The lane's main P5.2 construction produces an actual domain solution on a
genuine bounded box from the registered source packet. -/
def assembledSolution : ClassicalSolutionOmega (1 : ℝ) unitBox
    (0 : SpatialField) data.assembledForce 1 :=
  data.solution

/-- Its time interval, region, and domain are all inhabited. -/
theorem domains_inhabited : ∃ t : ℝ, t ∈ Ioo (0 : ℝ) 1 ∧
    ∃ x : Space, x ∈ Metric.ball (centers 0) (radii 0) ∧ x ∈ unitBox := by
  exact ⟨1 / 2, by norm_num, center,
    by simpa only [centers] using Metric.mem_ball_self (radius_pos 0), center_mem_unitBox⟩

#print axioms Rev497Nonvacuity.assembledSolution
#print axioms Rev497Nonvacuity.domains_inhabited

end Rev497Nonvacuity
