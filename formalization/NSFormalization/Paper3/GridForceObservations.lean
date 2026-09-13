import NSFormalization.Paper3.GridObservations
import NSFormalization.Paper3.TimeObservations

/-! Every-cell force observations derived from the actual time-dependent
conservative momentum balance. No equality of observations is a hypothesis. -/

noncomputable section
namespace NSFormalization.Paper3
open Set MeasureTheory NavierStokes NavierStokes.ProblemStatement
open NavierStokes.R3CompactIntegration

/-- Every cell sees identical force averages when the perturbation satisfies
compact conservative momentum balance and fits inside one cell interior. -/
theorem all_force_cell_averages_add_eq (grid : CartesianGrid)
    {w : ℝ × Space → Space} {z force reference : Space → Space}
    {a b t : ℝ} {K : Set Space} {flux : Fin 3 → Fin 3 → Space → ℝ}
    (hK : IsCompact K) (hw : ContDiffOn ℝ 1 w (Icc a b ×ˢ univ))
    (hsupp : ∀ r ∈ Icc a b, ∀ x ∉ K, w (r, x) = 0)
    (hdiv : ∀ r ∈ Icc a b, ∀ x, Comparator.divergence (fun y => w (r, y)) x = 0)
    (ht : t ∈ Ioo a b)
    (hderiv : ∀ x, HasDerivAt (fun r => w (r, x)) (z x) t)
    (hzint : ∀ j : Fin 3, Integrable (fun x => z x j))
    (hflux : ∀ j i, ContDiff ℝ 1 (flux j i))
    (hfluxc : ∀ j i, HasCompactSupport (flux j i))
    (hbalance : ∀ j x, force x j = z x j + ∑ i, spatialPartial i (flux j i) x)
    (hforceint : ∀ j : Fin 3, Integrable (fun x => force x j))
    (k₀ : Fin 3 → ℤ) (hsub : Function.support force ⊆ grid.cellInterior k₀)
    (k : Fin 3 → ℤ) (j : Fin 3)
    (href : IntegrableOn (fun x => reference x j) (grid.cell k)) :
    componentCellAverage (grid.cell k) (fun x => reference x + force x) j =
      componentCellAverage (grid.cell k) reference j := by
  classical
  by_cases hk : k = k₀
  · subst k
    have hzero : (∫ x : Space, force x j) = 0 :=
      integral_timeDependent_force_eq_zero hK hw hsupp hdiv ht hderiv j (hzint j)
        (hflux j) (hfluxc j) (hbalance j)
    have hzeroC : (∫ x in grid.cell k₀, force x j) = 0 := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero, hzero]
      intro x hx
      have hz : force x = 0 := by
        by_contra hn
        exact hx (grid.cellInterior_subset_cell k₀ (hsub hn))
      simp [hz]
    unfold componentCellAverage
    change (volume (grid.cell k₀)).toReal⁻¹ *
      (∫ x in grid.cell k₀, reference x j + force x j) = _
    rw [integral_add href (hforceint j).integrableOn, hzeroC, add_zero]
  · exact componentCellAverage_add_eq_of_disjoint (grid.measurableSet_cell k)
      ((grid.cell_disjoint_interior hk).mono_right hsub) j

end NSFormalization.Paper3
