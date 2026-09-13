import NSFormalization.Source.InsertionFamily
import NSFormalization.Paper3.ActualGridObservations
import NSFormalization.Paper3.CellIntegrability

/-! Actual fixed-profile singular families preserve all finite-grid cell observations. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff
namespace NSFormalization.Source.GridInsertionFamily
open NavierStokes.ProblemStatement NavierStokesR3.CompactEnergy
open NSFormalization.Paper3 InsertionFamily

/-- The actual insertion properties imply every-cell velocity and force
observation equality on the entire presingular interval, including time zero.
Cell integrability follows from continuity and bounded Cartesian cells. -/
theorem observations_of_insertionProperties {J : Type*} [Fintype J]
    (grids : J → CartesianGrid) {ν r T τ : ℝ} {x₀ : Space}
    {v g V G : VelocityField} {q Q : PressureField}
    (hv : ContDiff ℝ ∞ v) (hq : ContDiff ℝ ∞ q) (hg : ContDiff ℝ ∞ g)
    (hvdiv : ∀ t x, spatialDivergence v t x = 0)
    (hvNS : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, residual ν v q t x = g (t, x))
    (hτ0 : 0 ≤ τ)
    (h : InsertionProperties ν v q g x₀ r T τ V Q G)
    (indices : J → Fin 3 → ℤ)
    (hball : ∀ j, Metric.ball x₀ r ⊆ (grids j).cellInterior (indices j)) :
    ∀ t ∈ Ico (0 : ℝ) T, ∀ j k i,
      componentCellAverage ((grids j).cell k) (fun x => V (t, x)) i =
        componentCellAverage ((grids j).cell k) (fun x => v (t, x)) i ∧
      componentCellAverage ((grids j).cell k) (fun x => g (t, x) + G (t, x)) i =
        componentCellAverage ((grids j).cell k) (fun x => g (t, x)) i := by
  obtain ⟨hVs, hQs, hGs, hGc, hGloc, ⟨L, hLc, hLb, hLs⟩,
    hdiv, hNS, hSpeed, hLocal, hEarly⟩ := h
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    have hvel : (fun x => V (0, x)) = (fun x => v (0, x)) :=
      funext (fun x => (hEarly 0 hτ0 x).1)
    have hforce : (fun x => g (0, x) + G (0, x)) = (fun x => g (0, x)) := by
      funext x
      have hz : G (0, x) = 0 := image_eq_zero_of_notMem_tsupport
        (fun hx => (not_lt_of_ge hτ0) (hGloc hx).1)
      rw [hz, add_zero]
    intro j k i
    rw [hvel, hforce]
    exact ⟨rfl, rfl⟩
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    let a := t / 2
    let b := (t + T) / 2
    have hab : Icc a b ⊆ Ico (0 : ℝ) T := by
      intro s hs
      dsimp [a, b] at hs
      constructor <;> linarith [hs.1, hs.2, ht.2]
    have htab : t ∈ Ioo a b := by
      dsimp [a, b]
      constructor <;> linarith [ht.2]
    have hVab : ContDiffOn ℝ ∞ V (Icc a b ×ˢ univ) :=
      hVs.mono (Set.prod_mono hab Subset.rfl)
    have hQslice : ContDiff ℝ ∞ (fun x : Space => Q (t, x)) :=
      hQs.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun x => ⟨ht, mem_univ x⟩)
    have hqslice : ContDiff ℝ ∞ (fun x : Space => q (t, x)) :=
      hq.comp (contDiff_const.prodMk contDiff_id)
    have hsupp : ∀ s ∈ Icc a b, ∀ x ∉ L, (V - v) (s, x) = 0 := by
      intro s hs x hx
      exact image_eq_zero_of_notMem_tsupport (f := fun y => V (s, y) - v (s, y))
        (fun hn => hx ((hLs s (hab hs)).1 hn))
    have hpress : ∀ x ∉ L, (Q - q) (t, x) = 0 := by
      intro x hx
      exact image_eq_zero_of_notMem_tsupport (f := fun y => Q (t, y) - q (t, y))
        (fun hn => hx ((hLs t ht).2 hn))
    apply actual_finite_grid_velocity_force_observations grids hLc hVab hv.contDiffOn
      hQslice hqslice hsupp hpress (fun s hs => hdiv s (hab hs))
      (fun s _ => hvdiv s) (hNS t ⟨htpos, ht.2⟩) (hvNS t ⟨htpos, ht.2⟩)
      htab indices (fun j => hLb.trans (hball j))
    · intro j k i
      apply (grids j).integrableOn_cell_of_continuous k
      exact (EuclideanSpace.proj i).continuous.comp
        (hv.continuous.comp (continuous_const.prodMk continuous_id))
    · intro j k i
      apply (grids j).integrableOn_cell_of_continuous k
      exact (EuclideanSpace.proj i).continuous.comp
        (hg.continuous.comp (continuous_const.prodMk continuous_id))

/-- A finite family of Cartesian grids admits one actual fixed-profile
singular insertion family. Every sufficiently small member preserves every
velocity and force cell average for every 0 ≤ t < T. The same members retain
localized blowup and the no-continuation conclusion of InsertionProperties. -/
theorem exists_grid_insertion_family {J : Type*} [Fintype J]
    (grids : J → CartesianGrid) {ν : ℝ} (hν : 0 < ν)
    {v g : VelocityField} {q : PressureField}
    (hv : ContDiff ℝ ∞ v) (hq : ContDiff ℝ ∞ q) (hg : ContDiff ℝ ∞ g)
    (hvdiv : ∀ t x, spatialDivergence v t x = 0)
    {T τ : ℝ} (hτ0 : 0 ≤ τ) (hτT : τ < T)
    (hvNS : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, residual ν v q t x = g (t, x)) :
    ∃ x₀ : Space, ∃ r : ℝ, ∃ u : VelocityField, ∃ p : PressureField,
    ∃ f : VelocityField, ∃ K : Set Space, ∃ θ : Space → ℝ, ∃ η : ℝ → ℝ, ∃ ε₀ : ℝ,
      0 < r ∧ NavierStokesR3.ProblemStatement.CandidateProperties ν u p f K ∧
      IntegrableOn (dissipation u) (Ioo (0 : ℝ) 1) ∧
      ContDiff ℝ ∞ θ ∧ ContDiff ℝ ∞ η ∧
      HasCompactSupport θ ∧ HasCompactSupport η ∧ 0 < ε₀ ∧
      ∀ ε ∈ Ioo (0 : ℝ) ε₀,
        InsertionProperties ν v q g x₀ r T τ
          (velocity u v x₀ T θ η ε) (pressure p q x₀ T ε) (force ν f v x₀ T θ η ε) ∧
        ∀ t ∈ Ico (0 : ℝ) T, ∀ j k i,
          componentCellAverage ((grids j).cell k) (fun x => velocity u v x₀ T θ η ε (t, x)) i =
            componentCellAverage ((grids j).cell k) (fun x => v (t, x)) i ∧
          componentCellAverage ((grids j).cell k) (fun x => g (t, x) + force ν f v x₀ T θ η ε (t, x)) i =
            componentCellAverage ((grids j).cell k) (fun x => g (t, x)) i := by
  obtain ⟨x₀, r, hr, indices, hball⟩ := finite_grids_common_ball grids
  obtain ⟨u, p, f, K, θ, η, ε₀, hc, hD, hθ, hη, hθc, hηc, hε₀, hfamily⟩ :=
    exists_insertion_family hν hv hq hvdiv x₀ hr hτ0 hτT hvNS
  refine ⟨x₀, r, u, p, f, K, θ, η, ε₀, hr, hc, hD, hθ, hη, hθc, hηc, hε₀, ?_⟩
  intro ε hε
  exact ⟨hfamily ε hε, observations_of_insertionProperties grids hv hq hg hvdiv hvNS hτ0
    (hfamily ε hε) indices hball⟩

end NSFormalization.Source.GridInsertionFamily
