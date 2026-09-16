import Contracts.V1.Data
import NSFormalization.Paper3.GridObservations

/-!
# Geometric and locality lemmas for Theorem 4.7

This binding module states the two reusable ingredients of
`paper/sections/04-whole-space.tex:305-320` in the registered
`Contracts.V1.Data.Grid` / `Data.gridObservation` vocabulary.

The registered cells are half-open.  For the geometric lemma we first place
the ball in the open cell interior supplied by `Paper3.GridGeometry`, then
forget that strengthening.  For locality, support containment alone handles
all cells other than the containing cell.  Equality on the containing cell
requires the genuine zero-integral hypothesis used in the paper; local
integrability is included so that the Bochner integral of a difference splits.
-/

noncomputable section

namespace BlowupDensity.Bindings

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Paper3
open Contracts.V1.Data

/-- A finite family of registered Cartesian grids has a common positive-radius
ball contained in one (half-open) cell of every grid.

The final argument is retained to match the R47 construction interface.  The
paper imposes no location relative to that point, and the conclusion therefore
does not use it.  Internally, `finite_grids_common_ball` proves the stronger
containment in the corresponding open cell interiors. -/
theorem exists_ball_in_common_cell (n : ℕ) (grids : Fin n → Grid) (_x : Space) :
    ∃ x₀ r, 0 < r ∧ ∀ i, ∃ k, Metric.ball x₀ r ⊆ (grids i).cell k := by
  obtain ⟨x₀, r, hr, indices, hball⟩ := finite_grids_common_ball grids
  refine ⟨x₀, r, hr, fun i => ⟨indices i, ?_⟩⟩
  exact (hball i).trans ((grids i).cellInterior_subset_cell (indices i))

/-- Grid observations are local modulo the integral on the one containing
cell.  If the topological support of `z₁ - z₂` lies in `B`, `B` lies in one
cell, and the difference has zero integral on that cell, then every registered
cell average agrees.

The two integrability hypotheses are needed only on the containing cell.  They
exclude the totalized-Bochner-integral pathology in which an integral of a
difference cannot be split into the difference of the two integrals. -/
theorem gridObservation_locality (grid : Grid) (z₁ z₂ : SpatialField)
    (B : Set Space) (k₀ : Fin 3 → ℤ)
    (hsupport : tsupport (fun x => z₁ x - z₂ x) ⊆ B)
    (hB : B ⊆ grid.cell k₀)
    (hz₁ : IntegrableOn z₁ (grid.cell k₀))
    (hz₂ : IntegrableOn z₂ (grid.cell k₀))
    (hzero : (∫ x in grid.cell k₀, (z₁ x - z₂ x)) = 0) :
    gridObservation grid z₁ = gridObservation grid z₂ := by
  classical
  funext k
  unfold gridObservation cellAverage
  apply congrArg (fun w : Space => ((volume (grid.cell k)).toReal)⁻¹ • w)
  by_cases hk : k = k₀
  · subst k
    apply sub_eq_zero.mp
    rw [← integral_sub hz₁ hz₂]
    exact hzero
  · have hdisjoint : Disjoint (grid.cell k) (grid.cell k₀) := by
      obtain ⟨j, hj⟩ : ∃ j, k j ≠ k₀ j := by
        by_contra h
        push Not at h
        exact hk (funext h)
      apply Set.disjoint_left.mpr
      intro x hx hx₀
      have hkx := hx j
      have hk₀x := hx₀ j
      have hw := grid.width_pos j
      rcases lt_or_gt_of_ne hj with hj | hj
      · have hstep : k j + 1 ≤ k₀ j := by omega
        have hstep' : (k j : ℝ) + 1 ≤ (k₀ j : ℝ) := by exact_mod_cast hstep
        nlinarith
      · have hstep : k₀ j + 1 ≤ k j := by omega
        have hstep' : (k₀ j : ℝ) + 1 ≤ (k j : ℝ) := by exact_mod_cast hstep
        nlinarith
    apply setIntegral_congr_fun (grid.measurableSet_cell k)
    intro x hx
    by_contra hne
    exact Set.disjoint_left.mp hdisjoint hx
      (hB (hsupport (subset_tsupport _ (sub_ne_zero.mpr hne))))

end BlowupDensity.Bindings
