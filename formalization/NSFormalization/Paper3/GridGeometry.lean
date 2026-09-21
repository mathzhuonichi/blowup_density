import NavierStokes.ProblemStatement
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic
import Mathlib.Analysis.Real.Cardinality

/-! A finite family of actual Cartesian grids has a common interior ball. -/

noncomputable section
namespace NSFormalization.Paper3
open Set NavierStokes.ProblemStatement

/-- Each coordinate direction has its own positive spacing and offset. -/
structure CartesianGrid where
  offset : Fin 3 → ℝ
  width : Fin 3 → ℝ
  width_pos : ∀ j, 0 < width j

/-- Open interior of the cell with integer lattice index `k`. -/
def CartesianGrid.cellInterior (grid : CartesianGrid) (k : Fin 3 → ℤ) : Set Space :=
  {x | ∀ j, grid.offset j + grid.width j * (k j : ℝ) < x j ∧
    x j < grid.offset j + grid.width j * ((k j : ℝ) + 1)}

theorem CartesianGrid.isOpen_cellInterior (grid : CartesianGrid) (k : Fin 3 → ℤ) :
    IsOpen (grid.cellInterior k) := by
  have heq : grid.cellInterior k = ⋂ j : Fin 3, {x : Space |
    grid.offset j + grid.width j * (k j : ℝ) < x j ∧
    x j < grid.offset j + grid.width j * ((k j : ℝ) + 1)} := by
    ext x
    simp [CartesianGrid.cellInterior]
  rw [heq]
  apply isOpen_iInter_of_finite
  intro j
  exact (isOpen_lt continuous_const (EuclideanSpace.proj j).continuous).inter
    (isOpen_lt (EuclideanSpace.proj j).continuous continuous_const)

/-- Every finite family admits a point in the interior of one cell of every grid.
A diagonal point is chosen away from the countable set of all face coordinates. -/
theorem finite_grids_common_interior {G : Type*} [Fintype G] (grids : G → CartesianGrid) :
    ∃ x : Space, ∃ indices : G → Fin 3 → ℤ,
      ∀ g, x ∈ (grids g).cellInterior (indices g) := by
  let faceCoordinate : G × Fin 3 × ℤ → ℝ := fun a =>
    (grids a.1).offset a.2.1 + (grids a.1).width a.2.1 * (a.2.2 : ℝ)
  have hproper : Set.range faceCoordinate ≠ Set.univ := by
    intro h
    exact Set.not_countable_univ (h ▸ Set.countable_range faceCoordinate)
  obtain ⟨r, hr⟩ := Set.ne_univ_iff_exists_notMem _ |>.mp hproper
  let indices : G → Fin 3 → ℤ := fun g j =>
    ⌊(r - (grids g).offset j) / (grids g).width j⌋
  refine ⟨WithLp.toLp 2 (fun _ : Fin 3 => r), indices, ?_⟩
  intro g j
  change (grids g).offset j + (grids g).width j * (indices g j : ℝ) < r ∧
    r < (grids g).offset j + (grids g).width j * ((indices g j : ℝ) + 1)
  have hwidth := (grids g).width_pos j
  have hlo := Int.floor_le ((r - (grids g).offset j) / (grids g).width j)
  have hhi := Int.lt_floor_add_one ((r - (grids g).offset j) / (grids g).width j)
  have hne : r ≠ (grids g).offset j + (grids g).width j * (indices g j : ℝ) := by
    intro heq
    exact hr ⟨(g, j, indices g j), heq.symm⟩
  have hlo' := (le_div_iff₀ hwidth).mp hlo
  have hhi' := (div_lt_iff₀ hwidth).mp hhi
  dsimp [indices] at *
  constructor
  · exact lt_of_le_of_ne (by nlinarith) (Ne.symm hne)
  · nlinarith

/-- An open Euclidean ball lies in one open cell of every prescribed grid. -/
theorem finite_grids_common_ball {G : Type*} [Fintype G] (grids : G → CartesianGrid) :
    ∃ x : Space, ∃ ε : ℝ, 0 < ε ∧ ∃ indices : G → Fin 3 → ℤ,
      ∀ g, Metric.ball x ε ⊆ (grids g).cellInterior (indices g) := by
  obtain ⟨x, indices, hx⟩ := finite_grids_common_interior grids
  have hopen : IsOpen (⋂ g, (grids g).cellInterior (indices g)) :=
    isOpen_iInter_of_finite fun g => (grids g).isOpen_cellInterior (indices g)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen x (Set.mem_iInter.mpr hx)
  refine ⟨x, ε, hε, indices, ?_⟩
  intro g y hy
  exact Set.mem_iInter.mp (hball hy) g

/-- Half-open cells fix a convention on grid faces and partition all of space. -/
def CartesianGrid.cell (grid : CartesianGrid) (k : Fin 3 → ℤ) : Set Space :=
  {x | ∀ j, grid.offset j + grid.width j * (k j : ℝ) ≤ x j ∧
    x j < grid.offset j + grid.width j * ((k j : ℝ) + 1)}

theorem CartesianGrid.cellInterior_subset_cell (grid : CartesianGrid) (k : Fin 3 → ℤ) :
    grid.cellInterior k ⊆ grid.cell k := by
  intro x hx j
  exact ⟨(hx j).1.le, (hx j).2⟩

/-- Any other grid cell is disjoint from the interior of the containing cell. -/
theorem CartesianGrid.cell_disjoint_interior (grid : CartesianGrid)
    {k l : Fin 3 → ℤ} (hkl : k ≠ l) : Disjoint (grid.cell k) (grid.cellInterior l) := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, k j ≠ l j := by
    by_contra h
    push Not at h
    exact hkl (funext h)
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hk := hx j
  have hl := hy j
  have hw := grid.width_pos j
  rcases lt_or_gt_of_ne hj with hj | hj
  · have hh : k j + 1 ≤ l j := by omega
    have hh' : (k j : ℝ) + 1 ≤ (l j : ℝ) := by exact_mod_cast hh
    nlinarith
  · have hh : l j + 1 ≤ k j := by omega
    have hh' : (l j : ℝ) + 1 ≤ (k j : ℝ) := by exact_mod_cast hh
    nlinarith

end NSFormalization.Paper3
