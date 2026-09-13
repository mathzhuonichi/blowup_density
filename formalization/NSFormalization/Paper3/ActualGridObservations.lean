import NSFormalization.Paper3.GridObservations
import NSFormalization.Paper3.ResidualSupport
import NSFormalization.Paper3.ResidualObservations

/-!
# Actual PDE forces and every-cell observations

The force equality below is derived from the Navier--Stokes residual, smoothness,
incompressibility and compact support. Neither force mean zero nor a conservative
flux representation is assumed. Constructing the singular solution to which this
mechanism applies remains part of the separate insertion theorem.
-/

noncomputable section
namespace NSFormalization.Paper3
open Set MeasureTheory NavierStokes NavierStokes.ProblemStatement
open scoped ContDiff

/-- Actual forces of two smooth incompressible trajectories have identical
averages in every grid cell if their velocity and pressure differences fit
inside a common compact set in the interior of one cell. -/
theorem actual_force_cell_averages_eq (grid : CartesianGrid)
    {u v : VelocityField} {p q : PressureField} {f g : Space → Space}
    {a b t ν : ℝ} {K : Set Space}
    (hK : IsCompact K)
    (hu : ContDiffOn ℝ ∞ u (Icc a b ×ˢ univ))
    (hv : ContDiffOn ℝ ∞ v (Icc a b ×ˢ univ))
    (hp : ContDiff ℝ ∞ (fun x => p (t, x)))
    (hq : ContDiff ℝ ∞ (fun x => q (t, x)))
    (hsupp : ∀ r ∈ Icc a b, ∀ x ∉ K, (u - v) (r, x) = 0)
    (hpressure : ∀ x ∉ K, (p - q) (t, x) = 0)
    (hdivu : ∀ r ∈ Icc a b, ∀ x, spatialDivergence u r x = 0)
    (hdivv : ∀ r ∈ Icc a b, ∀ x, spatialDivergence v r x = 0)
    (hf : ∀ x, NSFormalization.Source.residual ν u p t x = f x)
    (hg : ∀ x, NSFormalization.Source.residual ν v q t x = g x)
    (ht : t ∈ Ioo a b) (k₀ : Fin 3 → ℤ) (hKcell : K ⊆ grid.cellInterior k₀)
    (k : Fin 3 → ℤ) (j : Fin 3) (hgi : IntegrableOn (fun x => g x j) (grid.cell k)) :
    componentCellAverage (grid.cell k) f j = componentCellAverage (grid.cell k) g j := by
  classical
  have hsupport : Function.support (fun x => f x - g x) ⊆ K := by
    simpa only [hf, hg] using support_residual_difference_subset hK.isClosed hsupp hpressure ht (ν := ν)
  have hpc : HasCompactSupport (fun x => (p - q) (t, x)) :=
    HasCompactSupport.intro hK hpressure
  have hzero : (∫ x : Space, f x j - g x j) = 0 := by
    simpa only [hf, hg] using integral_residual_difference_component_eq_zero
      hK hu hv hp hq hsupp hpc hdivu hdivv ht j (ν := ν)
  have hi : Integrable (fun x : Space => f x j - g x j) := by
    simpa only [hf, hg] using integrable_residual_difference_component
      hK hu hv hp hq hsupp hpressure ht j (ν := ν)
  have hfg : (fun x => g x + (f x - g x)) = f := by
    funext x
    abel
  by_cases hk : k = k₀
  · subst k
    have hzeroC : (∫ x in grid.cell k₀, f x j - g x j) = 0 := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero, hzero]
      intro x hx
      have hz : f x - g x = 0 := by
        by_contra hn
        exact hx (grid.cellInterior_subset_cell k₀ (hKcell (hsupport hn)))
      exact congrArg (fun z : Space => z j) hz
    unfold componentCellAverage
    have hsplit : (fun x => f x j) = (fun x => g x j + (f x j - g x j)) := by
      funext x
      ring
    rw [hsplit, integral_add hgi hi.integrableOn, hzeroC, add_zero]
  · have h := componentCellAverage_add_eq_of_disjoint
      (u := fun x => f x - g x) (v := g) (grid.measurableSet_cell k)
      ((grid.cell_disjoint_interior hk).mono_right (hsupport.trans hKcell)) j
    rwa [hfg] at h

/-- The corresponding actual velocity observations on every grid cell. -/
theorem actual_velocity_cell_averages_eq (grid : CartesianGrid)
    {u v : Space → Space} {K : Set Space} (hK : IsCompact K)
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (hsupp : ∀ x ∉ K, u x - v x = 0)
    (hd : ∀ x, Comparator.divergence (fun y => u y - v y) x = 0)
    (k₀ : Fin 3 → ℤ) (hKcell : K ⊆ grid.cellInterior k₀)
    (k : Fin 3 → ℤ) (j : Fin 3) (hvi : IntegrableOn (fun x => v x j) (grid.cell k)) :
    componentCellAverage (grid.cell k) u j = componentCellAverage (grid.cell k) v j := by
  have hc : HasCompactSupport (fun x => u x - v x) := HasCompactSupport.intro hK hsupp
  have hsub : Function.support (fun x => u x - v x) ⊆ grid.cellInterior k₀ := by
    intro x hx
    apply hKcell
    by_contra hn
    exact hx (hsupp x hn)
  have h := all_cell_averages_add_eq grid (hu.sub hv) hc hd k₀ hsub k j hvi
  have heq : (fun x => v x + (u x - v x)) = u := by funext x; abel
  rwa [heq] at h

/-- The velocity/force observation interface for inserting any actual compact
PDE perturbation into a finite grid family. The common-cell sets are supplied
by `finite_grids_common_ball`; no observation equality is a premise. -/
theorem actual_finite_grid_velocity_force_observations
    {G : Type*} [Fintype G] (grids : G → CartesianGrid)
    {u v : VelocityField} {p q : PressureField} {f g : Space → Space}
    {a b t ν : ℝ} {K : Set Space}
    (hK : IsCompact K)
    (hu : ContDiffOn ℝ ∞ u (Icc a b ×ˢ univ))
    (hv : ContDiffOn ℝ ∞ v (Icc a b ×ˢ univ))
    (hp : ContDiff ℝ ∞ (fun x => p (t, x)))
    (hq : ContDiff ℝ ∞ (fun x => q (t, x)))
    (hsupp : ∀ r ∈ Icc a b, ∀ x ∉ K, (u - v) (r, x) = 0)
    (hpressure : ∀ x ∉ K, (p - q) (t, x) = 0)
    (hdivu : ∀ r ∈ Icc a b, ∀ x, spatialDivergence u r x = 0)
    (hdivv : ∀ r ∈ Icc a b, ∀ x, spatialDivergence v r x = 0)
    (hf : ∀ x, NSFormalization.Source.residual ν u p t x = f x)
    (hg : ∀ x, NSFormalization.Source.residual ν v q t x = g x)
    (ht : t ∈ Ioo a b) (indices : G → Fin 3 → ℤ)
    (hKcells : ∀ grid, K ⊆ (grids grid).cellInterior (indices grid))
    (hvi : ∀ grid k j, IntegrableOn (fun x => v (t, x) j) ((grids grid).cell k))
    (hgi : ∀ grid k j, IntegrableOn (fun x => g x j) ((grids grid).cell k)) :
    ∀ grid k j,
      componentCellAverage ((grids grid).cell k) (fun x => u (t, x)) j =
        componentCellAverage ((grids grid).cell k) (fun x => v (t, x)) j ∧
      componentCellAverage ((grids grid).cell k) f j =
        componentCellAverage ((grids grid).cell k) g j := by
  have ht' := Ioo_subset_Icc_self ht
  have hus := NavierStokes.PeriodicUniqueness.spatial_smooth hu ht'
  have hvs := NavierStokes.PeriodicUniqueness.spatial_smooth hv ht'
  have hd : ∀ x, Comparator.divergence (fun y => u (t, y) - v (t, y)) x = 0 := by
    intro x
    change Comparator.divergence (fun y => (u - v) (t, y)) x = 0
    rw [← ComparatorBridge.divergence_eq (u - v) t x]
    rw [NavierStokes.PeriodicUniqueness.spatialDivergence_sub hus hvs,
      hdivu t ht', hdivv t ht', sub_self]
  intro grid k j
  constructor
  · exact actual_velocity_cell_averages_eq (grids grid) hK
      (hus.of_le (by simp)) (hvs.of_le (by simp)) (hsupp t ht') hd
      (indices grid) (hKcells grid) k j (hvi grid k j)
  · exact actual_force_cell_averages_eq (grids grid) hK hu hv hp hq hsupp hpressure
      hdivu hdivv hf hg ht (indices grid) (hKcells grid) k j (hgi grid k j)

end NSFormalization.Paper3
