import Bindings.MultipleRegions

/-! Concrete non-vacuity of the registered `T04.multiple_regions` contract:
one quarter-ball at the centre of the fundamental cube, terminal time one,
and the registered blow-up packet at viscosity one. -/
noncomputable section
namespace MultipleRegionsNonvacuity

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

theorem api_nonempty :
    Nonempty (MultipleRegionsAPI packet 1 centres radii) :=
  BlowupDensity.Bindings.multipleRegionsStatement_holds
    1 one_pos packet 1 one_pos 1 one_pos centres radii
      radius_pos region_interior regions_disjoint

def api : MultipleRegionsAPI packet 1 centres radii :=
  Classical.choice api_nonempty

/-- The concrete inhabitant really supplies blow-up in its one prescribed
quarter-ball. -/
theorem region_blowup_zero :
    SpeedUnboundedAtOn 1 (Metric.ball (centres 0) (radii 0))
      api.assembled_velocity :=
  api.region_blowup 0

end MultipleRegionsNonvacuity
