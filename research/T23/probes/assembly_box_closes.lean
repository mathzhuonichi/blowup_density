import Bindings.BoundaryInsertion
import Bindings.InsertionFromData
import NSFormalization.Section3.T22.Assembly

noncomputable section
namespace T23U9FullProbe
open Set MeasureTheory
open NSFormalization.Section3.T23
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
def Ω₀ : Set Space :=
  {x : Space | ∀ i : Fin 3, (0 : ℝ) < x i ∧ x i < 1}

theorem Ω₀_isBox : IsBoxDomain Ω₀ := by
  exact ⟨(fun _ => 0), (fun _ => 1), (fun _ => zero_lt_one), rfl⟩

theorem zero_initial (Ω : Set Space) :
    (0 : SpatialField) ∈ initialClassOmega Ω := by
  refine ⟨contDiffOn_const, ?_, ?_⟩
  · intro x hx
    simp [spatialDivergence, spatialDerivative]
  · intro x hx
    rfl

theorem zero_force (Ω : Set Space) :
    (0 : SpaceTimeField) ∈ forceClassOmega Ω := by
  refine ⟨?_, ⟨∅, isCompact_empty, empty_subset _, ?_⟩⟩
  · intro T
    exact ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
  · simp

def zeroSolution (ν T : ℝ) (hT : 0 < T) :
    ClassicalSolutionOmega ν Ω₀ 0 0 T where
  velocity := 0
  pressure := 0
  horizon_pos := hT
  velocity_smooth := ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
  pressure_smooth := ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
  initial := fun _ _ => rfl
  divergence := by
    intro t ht x hx
    simp [spatialDivergence, spatialDerivative]
  momentum := by
    intro t ht x hx
    simp [NavierStokesR3.ProblemStatement.navierStokesResidual, temporalDerivative,
      advection, spatialDerivative, spatialLaplacian, pressureGradient]
  no_slip := by
    intro t ht x hx
    rfl
  pressure_gauge := by
    intro t ht
    simp


def centre : Space := WithLp.toLp 2 (fun _ : Fin 3 => (1 / 2 : ℝ))

theorem ball_in_box : closure (Metric.ball centre (1 / 4 : ℝ)) ⊆ Ω₀ := by
  intro x hx i
  have hd : ‖x - centre‖ ≤ 1 / 4 := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using Metric.closure_ball_subset_closedBall hx
  have hc := PiLp.norm_apply_le (x - centre) i
  change |x i - 1 / 2| ≤ ‖x - centre‖ at hc
  have hh := abs_le.mp (hc.trans hd)
  exact ⟨by linarith [hh.1], by linarith [hh.2]⟩

def packet := BlowupDensity.Bindings.insertionFromData_packet 1 one_pos

def place : DomainPlacementData packet.velocity packet.pressure packet.force packet.carrier :=
  domainPlacementData packet.carrier_compact packet.force_support.1 centre (1 / 4)
    (by norm_num) ball_in_box centre (Metric.mem_ball_self (by norm_num)) 1 one_pos

theorem full_api_nonempty : ∃ D : CutoffData,
    Nonempty (BoundaryInsertionAPI 1 packet.velocity packet.pressure packet.force packet.carrier
      packet.energyBound packet.dissipationBound place Ω₀ NSFormalization.Section3.T22.boundedDomainNorm
      0 0 (1 / 8) 1 D (zeroSolution 1 (place.T + 1) (by norm_num [place, domainPlacementData]))) := by
  have hΩ : IsBoundedBoxOrSmoothDomain Ω₀ :=
    ⟨Ω₀_isBox.open_bounded.1, Ω₀_isBox.open_bounded.2,
      ⟨centre, fun _ => ⟨by norm_num [centre], by norm_num [centre]⟩⟩, Or.inl Ω₀_isBox⟩
  obtain ⟨_, D, _, _, _, _, _, _, _, _, _, _, _, _, hapi⟩ :=
    BlowupDensity.Bindings.BoundaryInsertion.boundaryInsertionStatement'_of_ibp packet
      BlowupDensity.Bindings.thresholds place Ω₀ NSFormalization.Section3.T22.boundedDomainNorm
      0 0 (1 / 8) 1 (zeroSolution 1 (place.T + 1) (by norm_num [place, domainPlacementData])) hΩ (ibp_box Ω₀_isBox)
      one_pos (by norm_num) (zero_force Ω₀) (zero_initial Ω₀)
      (Metric.closure_ball_subset_closedBall.trans (Metric.closedBall_subset_ball (by norm_num [place, domainPlacementData]))) ball_in_box
  exact ⟨D, hapi⟩

/-- This probe's packet is the actual singular registered packet. -/
theorem packet_nonzero : packet.velocity ≠ 0 := by
  intro h
  obtain ⟨t, x, _, _, hb⟩ := packet.speed_unbounded 1 one_pos 1 one_pos
  rw [h] at hb
  norm_num at hb

end T23U9FullProbe

/-- info: 'T23U9FullProbe.full_api_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms T23U9FullProbe.full_api_nonempty
/-- info: 'T23U9FullProbe.packet_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms T23U9FullProbe.packet_nonzero
