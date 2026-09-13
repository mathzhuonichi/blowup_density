import NavierStokes.R3EnergyNorms
import NavierStokes.R3CompactParametricIntegral

/-!
# Uniform norms of a smooth compact comparison field

Compactness gives the `L²`, `L⁶`, sup-norm, and gradient bounds used in the
comparison argument. These are conclusions from the field's support and
smoothness assumptions.
-/

noncomputable section
namespace NavierStokes.R3UniformBounds

open Set Filter MeasureTheory ProblemStatement
open scoped ContDiff Topology ENNReal

structure Bounds (I : Set ℝ) (u : VelocityField) (V : ℝ) : Prop where
  nonneg : 0 ≤ V
  pointwise : ∀ t ∈ I, ∀ x, ‖u (t, x)‖ ≤ V
  memLp_two : ∀ t ∈ I, MemLp (fun x => ‖u (t, x)‖) 2
  memLp_six : ∀ t ∈ I, MemLp (fun x => ‖u (t, x)‖) 6
  memLp_top : ∀ t ∈ I, MemLp (fun x => ‖u (t, x)‖) ⊤
  norm_two : ∀ t ∈ I, lpNorm (fun x => ‖u (t, x)‖) 2 volume ≤ V
  norm_six : ∀ t ∈ I, lpNorm (fun x => ‖u (t, x)‖) 6 volume ≤ V
  norm_top : ∀ t ∈ I, lpNorm (fun x => ‖u (t, x)‖) ⊤ volume ≤ V

theorem exists_bounds {I : Set ℝ} (hI : IsCompact I) {K : Set Space} (hK : IsCompact K)
    {u : VelocityField} (hu : ContinuousOn u (I ×ˢ (univ : Set Space)))
    (hsupp : ∀ t ∈ I, ∀ x ∉ K, u (t, x) = 0) : ∃ V : ℝ, Bounds I u V := by
  obtain ⟨C, hC⟩ := (hI.prod hK).exists_bound_of_continuousOn
    (hu.mono (prod_mono Subset.rfl (subset_univ K)))
  let A := max C 0
  have hA : 0 ≤ A := le_max_right _ _
  let m : Space → ℝ := K.indicator (fun _ => A)
  have hm (p : ℝ≥0∞) : MemLp m p := memLp_indicator_const p hK.measurableSet A (Or.inr hK.measure_ne_top)
  have hmajor (t : ℝ) (ht : t ∈ I) (x : Space) : ‖u (t, x)‖ ≤ m x := by
    by_cases hx : x ∈ K
    · simpa only [m, indicator_of_mem hx] using (hC (t, x) ⟨ht, hx⟩).trans (le_max_left _ _)
    · simp only [m, indicator_of_notMem hx, hsupp t ht x hx, norm_zero, le_refl]
  have huc (t : ℝ) (ht : t ∈ I) : Continuous (fun x : Space => u (t, x)) :=
    R3CompactParametricIntegral.continuous_slice hu ht
  have hMem (p : ℝ≥0∞) (t : ℝ) (ht : t ∈ I) : MemLp (fun x => ‖u (t, x)‖) p := by
    apply (hm p).mono' (huc t ht).norm.aestronglyMeasurable
    filter_upwards with x
    simpa only [norm_norm] using hmajor t ht x
  have hNorm (p : ℝ≥0∞) (t : ℝ) (ht : t ∈ I) :
      lpNorm (fun x => ‖u (t, x)‖) p volume ≤ lpNorm m p volume := by
    apply lpNorm_mono_real (hm p)
    intro x
    simpa only [norm_norm] using hmajor t ht x
  let V := A + lpNorm m 2 volume + lpNorm m 6 volume + lpNorm m ⊤ volume
  have h₂ : 0 ≤ lpNorm m 2 volume := lpNorm_nonneg
  have h₆ : 0 ≤ lpNorm m 6 volume := lpNorm_nonneg
  have hi : 0 ≤ lpNorm m ⊤ volume := lpNorm_nonneg
  refine ⟨V, ?_⟩
  constructor
  · dsimp [V]; positivity
  · intro t ht x
    have hb : m x ≤ A := by
      by_cases hx : x ∈ K <;> simp [m, hx, hA]
    exact ((hmajor t ht x).trans hb).trans (by dsimp [V]; linarith)
  · exact hMem 2
  · exact hMem 6
  · exact hMem ⊤
  · intro t ht
    exact (hNorm 2 t ht).trans (by dsimp [V]; linarith)
  · intro t ht
    exact (hNorm 6 t ht).trans (by dsimp [V]; linarith)
  · intro t ht
    exact (hNorm ⊤ t ht).trans (by dsimp [V]; linarith)

theorem exists_global_gradient_bound {a b : ℝ} (hab : a < b) {K : Set Space} (hK : IsCompact K)
    {u : VelocityField} (hu : ContDiffOn ℝ ∞ u (PeriodicUniqueness.slab a b))
    (hsupp : ∀ t ∈ Icc a b, ∀ x ∉ K, u (t, x) = 0) :
    ∃ B : ℝ, 0 < B ∧ ∀ t ∈ Icc a b, ∀ x, ‖spatialDerivative u t x‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := PeriodicUniqueness.exists_gradient_bound hab hu hK
  refine ⟨B, hB, ?_⟩
  intro t ht x
  by_cases hx : x ∈ K
  · exact hb t ht x hx
  · have he : (fun y : Space => u (t, y)) =ᶠ[𝓝 x] (fun _ => (0 : Space)) := by
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
      exact hsupp t ht y hy
    have hd := he.fderiv_eq (𝕜 := ℝ)
    simpa only [spatialDerivative, hd, fderiv_const_apply, norm_zero] using hB.le

theorem vector_memLp {u : Space → Space} (hu : Continuous u) (hU : MemLp (fun x => ‖u x‖) 2) :
    MemLp u 2 := (memLp_norm_iff hu.aestronglyMeasurable).mp hU

theorem norm_le_of_energy_bound {u : Space → Space} (hu : AEStronglyMeasurable u volume) {E : ℝ}
    (hE : (∫ x : Space, ‖u x‖ ^ 2) ≤ E) : lpNorm u 2 volume ≤ |E| + 1 := by
  have he := R3EnergyNorms.lpNorm_two_sq hu
  have hn : 0 ≤ lpNorm u 2 volume := lpNorm_nonneg
  nlinarith [abs_nonneg E, le_abs_self E, sq_nonneg (|E|)]

end NavierStokes.R3UniformBounds
