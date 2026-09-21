import NSFormalization.Paper3.GridObservations
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Smooth reference fields need only cellwise integrability on finite cells. -/
noncomputable section
namespace NSFormalization.Paper3
open Set MeasureTheory NavierStokes.ProblemStatement

/-- Each half-open Cartesian cell lies in an explicitly compact closed box. -/
theorem CartesianGrid.cell_subset_compact (grid : CartesianGrid) (k : Fin 3 → ℤ) :
    ∃ K : Set Space, IsCompact K ∧ grid.cell k ⊆ K := by
  let lo : Fin 3 → ℝ := fun j => grid.offset j + grid.width j * (k j : ℝ)
  let hi : Fin 3 → ℝ := fun j => grid.offset j + grid.width j * ((k j : ℝ) + 1)
  let box : Set (Fin 3 → ℝ) := Set.pi univ (fun j => Icc (lo j) (hi j))
  have hbox : IsCompact box := isCompact_univ_pi (fun _ => isCompact_Icc)
  refine ⟨WithLp.toLp 2 '' box, hbox.image (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)), ?_⟩
  intro x hx
  refine ⟨WithLp.ofLp x, ?_, by simp⟩
  intro j _
  exact ⟨(hx j).1, (hx j).2.le⟩

/-- No global spatial integrability of the reference is necessary: continuity
on the compact closed box enclosing each cell suffices. -/
theorem CartesianGrid.integrableOn_cell_of_continuous (grid : CartesianGrid)
    (k : Fin 3 → ℤ) {f : Space → ℝ} (hf : Continuous f) :
    IntegrableOn f (grid.cell k) := by
  obtain ⟨K, hK, hsub⟩ := grid.cell_subset_compact k
  exact (hf.continuousOn.integrableOn_compact hK).mono_set hsub

end NSFormalization.Paper3
