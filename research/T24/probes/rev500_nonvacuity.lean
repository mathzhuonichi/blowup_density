import NSFormalization.Section3.T24.MultipleOmegaRegions
import NSFormalization.Section3.T23.DifferenceEnergy
import NSFormalization.Section3.T15.Assembly
import Bindings.PacketImport

/-! Reviewer non-vacuity check: one actual registered packet, one region, and the
open unit box.  This instantiates all four lane-500 theorems without assuming a
`MultipleRegionsOmegaAPI` inhabitant. -/
noncomputable section
set_option linter.unusedVariables false

namespace Rev500Nonvacuity

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T13 NSFormalization.Section3.T15
open NSFormalization.Section3.T23 NSFormalization.Section3.T24
open NSFormalization.Section3.T24.OmegaRegions
open NSFormalization.Source.PacketScaling (zeroPastField)
open scoped ENNReal Topology

def unitBox : Set Space := fundamentalCubeInterior
def center : Space := placementCenter
def radius : ℝ := 3 / 8

theorem unitBox_isBox : IsBoxDomain unitBox := by
  refine ⟨fun _ => 0, fun _ => 1, fun _ => by norm_num, ?_⟩
  rfl

theorem center_mem_unitBox : center ∈ unitBox := by
  intro i
  change 0 < (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) < 1
  norm_num

theorem unitBox_domain : IsBoundedBoxOrSmoothDomain unitBox := by
  have hob := unitBox_isBox.open_bounded
  exact ⟨hob.1, hob.2, ⟨center, center_mem_unitBox⟩, Or.inl unitBox_isBox⟩

theorem ball_in_unitBox : closure (Metric.ball center radius) ⊆ unitBox := by
  simpa [unitBox, center, radius, interior_fundamentalCube] using placement_chart_in_cube

def P : BlowupDensity.Contracts.V1.PacketImportAPI 1 :=
  BlowupDensity.Bindings.packetImportFamily.select 1 zero_lt_one

theorem packet : NSFormalization.Section4.I03.PacketData
    P.velocity P.carrier P.energyBound P.dissipationBound :=
  ⟨P.velocity_extension_smooth, P.carrier_compact, P.velocity_support,
    P.square_integrable, P.zero_initial_velocity, P.energy_isLUB,
    P.dissipation_integrable, P.dissipation_eq⟩

def place : DomainPlacementData P.velocity P.pressure P.force P.carrier :=
  domainPlacementData P.carrier_compact P.force_support.1 center radius
    (by norm_num [radius]) ball_in_unitBox center (Metric.mem_ball_self (by norm_num [radius]))
    1 zero_lt_one

def placement : Fin 1 → DomainPlacementData P.velocity P.pressure P.force P.carrier :=
  fun _ => place

def epsilon : Fin 1 → ℝ := fun _ => place.ε₀

def component : Fin 1 → VelocityField :=
  fun _ => scaledVelocity P.velocity place.x₀ 1 place.ε₀

theorem regions_disjoint : Pairwise (fun i j : Fin 1 =>
    Disjoint (Metric.ball center radius) (Metric.ball center radius)) := by
  intro i j hij
  exact (hij (Subsingleton.elim i j)).elim

theorem eps_admissible (j : Fin 1) :
    epsilon j ∈ Ioc (0 : ℝ) (placement j).ε₀ :=
  ⟨place.eps_pos, le_rfl⟩

theorem eps_time (j : Fin 1) : epsilon j ^ 2 < (1 : ℝ) := by
  have h := (placement j).eps_time (epsilon j) (eps_admissible j)
  change 2 * epsilon j ^ 2 < (1 : ℝ) at h
  nlinarith [sq_nonneg (epsilon j)]

theorem placement_time (j : Fin 1) : (placement j).T = (1 : ℝ) := rfl

theorem placement_chart (j : Fin 1) :
    (placement j).chartCenter = center ∧ (placement j).chartRadius = radius :=
  ⟨rfl, rfl⟩

theorem component_pin (j : Fin 1) :
    component j = scaledVelocity P.velocity (placement j).x₀ 1 (epsilon j) := rfl

theorem component_support (j : Fin 1) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1)
    (x : Space) (hout : x ∉ Metric.ball center radius) : component j (t, x) = 0 := by
  change scaledVelocity P.velocity (placement j).x₀ 1 (epsilon j) (t, x) = 0
  by_contra hne
  apply hout
  apply affineImage_subset_ball (eps_admissible j) (placement j).eps_space
  exact scaledVelocity_tsupp_subset (eps_admissible j).1 P.carrier_compact
    P.velocity_support (placement j).carrier_subset ht.2 (subset_tsupport _ hne)

theorem concrete_region_agreement : ∀ j : Fin 1, ∀ t ∈ Ico (0 : ℝ) 1,
    ∀ x ∈ Metric.ball center radius,
      assembledVelocity component (t, x) = component j (t, x) :=
  region_agreement regions_disjoint component_support

theorem concrete_region_blowup : ∀ j : Fin 1,
    SpeedUnboundedAtOn 1 (Metric.ball center radius) (assembledVelocity component) :=
  region_blowup regions_disjoint component_support component_pin
    (fun j => (eps_admissible j).1) eps_time P.speed_unbounded

theorem concrete_energy_bound :
    energyEssSupOmega unitBox 1 (assembledVelocity component) ^ (2 : ℕ) ≤
      ENNReal.ofReal (P.energyBound ^ 2 * ∑ j, epsilon j) :=
  energy_bound regions_disjoint component_support placement packet eps_admissible
    component_pin (fun _ => ball_in_unitBox)

theorem concrete_dissipation_bound :
    energyGradientOmega unitBox 1 (assembledVelocity component) ^ (2 : ℕ) =
      ENNReal.ofReal (P.dissipationBound ^ 2 * ∑ j, epsilon j) :=
  dissipation_bound regions_disjoint placement packet placement_time placement_chart
    eps_admissible component_pin (fun _ => ball_in_unitBox)

theorem domains_inhabited :
    ∃ j : Fin 1, ∃ t : ℝ, t ∈ Ioo (0 : ℝ) 1 ∧
      ∃ x : Space, x ∈ Metric.ball center radius ∧ x ∈ unitBox := by
  refine ⟨0, 1 / 2, by norm_num, center, Metric.mem_ball_self (by norm_num [radius]), ?_⟩
  exact ball_in_unitBox (subset_closure (Metric.mem_ball_self (by norm_num [radius])))

#print axioms Rev500Nonvacuity.concrete_region_agreement
#print axioms Rev500Nonvacuity.concrete_region_blowup
#print axioms Rev500Nonvacuity.concrete_energy_bound
#print axioms Rev500Nonvacuity.concrete_dissipation_bound
#print axioms Rev500Nonvacuity.domains_inhabited

end Rev500Nonvacuity
