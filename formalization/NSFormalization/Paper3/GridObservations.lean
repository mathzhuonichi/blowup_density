import NSFormalization.Paper3.GridGeometry
import NSFormalization.Paper3.CompactObservations

/-! Exact observations on every cell of every grid in a finite family.
These theorems concern actual compact solenoidal perturbations and Lebesgue
cell averages. Existence of a singular PDE perturbation is a separate result. -/

noncomputable section
namespace NSFormalization.Paper3
open Set MeasureTheory NavierStokes NavierStokes.ProblemStatement

 theorem CartesianGrid.measurableSet_cell (grid : CartesianGrid) (k : Fin 3 → ℤ) :
    MeasurableSet (grid.cell k) := by
  have heq : grid.cell k = ⋂ j : Fin 3, {x : Space |
      grid.offset j + grid.width j * (k j : ℝ) ≤ x j ∧
      x j < grid.offset j + grid.width j * ((k j : ℝ) + 1)} := by
    ext x
    simp [CartesianGrid.cell]
  rw [heq]
  apply MeasurableSet.iInter
  intro j
  exact (isClosed_le continuous_const (EuclideanSpace.proj j).continuous).measurableSet.inter
    (isOpen_lt (EuclideanSpace.proj j).continuous continuous_const).measurableSet

 theorem componentCellAverage_add_eq_of_disjoint {u v : Space → Space}
    {C : Set Space} (hC : MeasurableSet C) (hdis : Disjoint C (Function.support u))
    (j : Fin 3) :
    componentCellAverage C (fun x => v x + u x) j = componentCellAverage C v j := by
  unfold componentCellAverage
  congr 1
  apply setIntegral_congr_fun hC
  intro x hx
  have hz : u x = 0 := by
    by_contra hn
    exact Set.disjoint_left.mp hdis hx hn
  simp [hz]

/-- A compact solenoidal perturbation inside one open cell is invisible on
all cells, including all cells outside its support. -/
theorem all_cell_averages_add_eq (grid : CartesianGrid)
    {u v : Space → Space} (hu : ContDiff ℝ 1 u) (hs : HasCompactSupport u)
    (hd : ∀ x, Comparator.divergence u x = 0)
    (k₀ : Fin 3 → ℤ) (hsub : Function.support u ⊆ grid.cellInterior k₀)
    (k : Fin 3 → ℤ) (j : Fin 3) (hv : IntegrableOn (fun x => v x j) (grid.cell k)) :
    componentCellAverage (grid.cell k) (fun x => v x + u x) j =
      componentCellAverage (grid.cell k) v j := by
  classical
  by_cases hk : k = k₀
  · subst k
    exact componentCellAverage_add_eq hu hs hd (grid.measurableSet_cell k₀)
      (hsub.trans (grid.cellInterior_subset_cell k₀)) j hv
  · exact componentCellAverage_add_eq_of_disjoint (grid.measurableSet_cell k)
      ((grid.cell_disjoint_interior hk).mono_right hsub) j

/-- One ball makes every compact solenoidal velocity perturbation supported
there invisible to every cell of every prescribed grid. -/
theorem finite_grids_invisible_ball {G : Type*} [Fintype G] (grids : G → CartesianGrid) :
    ∃ x : Space, ∃ ε : ℝ, 0 < ε ∧
      ∀ (u v : Space → Space), ContDiff ℝ 1 u → HasCompactSupport u →
      (∀ y, Comparator.divergence u y = 0) → Function.support u ⊆ Metric.ball x ε →
      ∀ (g : G) (k : Fin 3 → ℤ) (j : Fin 3),
      IntegrableOn (fun y => v y j) ((grids g).cell k) →
      componentCellAverage ((grids g).cell k) (fun y => v y + u y) j =
        componentCellAverage ((grids g).cell k) v j := by
  obtain ⟨x, ε, hε, indices, hball⟩ := finite_grids_common_ball grids
  refine ⟨x, ε, hε, ?_⟩
  intro u v hu hs hd hsub g k j hv
  exact all_cell_averages_add_eq (grids g) hu hs hd (indices g)
    (hsub.trans (hball g)) k j hv

end NSFormalization.Paper3
