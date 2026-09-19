import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Boundary flux cancellation on coordinate boxes. -/
noncomputable section
namespace NSFormalization.Section3.T23
open Set MeasureTheory
open scoped ContDiff

/-- Either face of a nondegenerate coordinate box belongs to its frontier. -/
theorem box_face_mem_frontier (a b : Fin 3 → ℝ) (hab : ∀ i, a i < b i)
    (i : Fin 3) (c : ℝ) (hc : c = a i ∨ c = b i)
    (x : Fin 2 → ℝ) (hx : x ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :
    i.insertNth c x ∈ frontier (Icc a b) := by
  rw [frontier, isClosed_Icc.closure_eq]
  refine ⟨?_, ?_⟩
  · constructor
    · rw [Fin.le_insertNth_iff]
      exact ⟨hc.elim (fun h => h ▸ le_rfl) (fun h => h ▸ (hab i).le), hx.1⟩
    · rw [Fin.insertNth_le_iff]
      exact ⟨hc.elim (fun h => h ▸ (hab i).le) (fun h => h ▸ le_rfl), hx.2⟩
  · rw [← pi_univ_Icc, interior_pi_set (finite_univ), show
        (fun j => interior (Icc (a j) (b j))) = (fun j => Ioo (a j) (b j)) from
        funext (fun _ => interior_Icc)]
    intro h
    have hi := h i (mem_univ i)
    simp only [Fin.insertNth_apply_same, mem_Ioo] at hi
    rcases hc with rfl | rfl
    · exact (lt_irrefl _ hi.1)
    · exact (lt_irrefl _ hi.2)

end NSFormalization.Section3.T23
