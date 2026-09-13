import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Recovering pointwise inequalities from smooth time tests

This permits a distributional pressure pairing bound to control the
continuous, spatially localized physical pressure flux at every time.
-/

noncomputable section
namespace NavierStokes.R3PositiveTests

open Set Filter MeasureTheory
open scoped Topology ContDiff

theorem continuous_test_product {s : Set ℝ} (hs : IsOpen s) {b f : ℝ → ℝ}
    (hb : Continuous b) (hf : ContinuousOn f s) (hbs : tsupport b ⊆ s) :
    Continuous (fun t => b t * f t) := by
  exact (hb.continuousOn.mul hf).continuous_of_tsupport_subset hs
    (tsupport_mul_subset_left.trans hbs)

theorem le_of_test_integrals {s : Set ℝ} (hs : IsOpen s) {f g : ℝ → ℝ}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (htest : ∀ b : ℝ → ℝ, ContDiff ℝ ∞ b → HasCompactSupport b → tsupport b ⊆ s →
      (∀ t, 0 ≤ b t) → (∫ t : ℝ, b t * f t) ≤ ∫ t : ℝ, b t * g t) :
    ∀ t ∈ s, f t ≤ g t := by
  intro t ht
  by_contra hn
  have hpos : 0 < f t - g t := sub_pos.mpr (lt_of_not_ge hn)
  have hnh : s ∩ {r | 0 < f r - g r} ∈ 𝓝 t :=
    inter_mem (hs.mem_nhds ht) (((hf.sub hg).continuousAt (hs.mem_nhds ht))
      (Ioi_mem_nhds hpos))
  obtain ⟨b, hbs, hbc, hbd, hbr, hbt⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) hnh
  have hbs' : tsupport b ⊆ s := hbs.trans inter_subset_left
  have hb₀ (r : ℝ) : 0 ≤ b r := (hbr (mem_range_self r)).1
  have hcont := continuous_test_product hs hbd.continuous (hf.sub hg) hbs'
  have hnonneg (r : ℝ) : 0 ≤ b r * (f r - g r) := by
    by_cases hr : b r = 0
    · simp [hr]
    · exact mul_nonneg (hb₀ r) (hbs (subset_tsupport _ hr)).2.le
  have hint : 0 < ∫ r : ℝ, b r * (f r - g r) :=
    hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hbc.mul_right hnonneg
      (by rw [hbt, one_mul]; exact hpos.ne')
  have hiF := (continuous_test_product hs hbd.continuous hf hbs').integrable_of_hasCompactSupport (μ := volume)
    (show HasCompactSupport (fun r => b r * f r) from hbc.mul_right)
  have hiG := (continuous_test_product hs hbd.continuous hg hbs').integrable_of_hasCompactSupport (μ := volume)
    (show HasCompactSupport (fun r => b r * g r) from hbc.mul_right)
  simp_rw [mul_sub] at hint
  rw [integral_sub hiF hiG] at hint
  have hb := htest b hbd hbc hbs' hb₀
  linarith

theorem abs_le_of_test_integrals {s : Set ℝ} (hs : IsOpen s) {f g : ℝ → ℝ}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (htest : ∀ b : ℝ → ℝ, ContDiff ℝ ∞ b → HasCompactSupport b → tsupport b ⊆ s →
      (∀ t, 0 ≤ b t) → |∫ t : ℝ, b t * f t| ≤ ∫ t : ℝ, b t * g t) :
    ∀ t ∈ s, |f t| ≤ g t := by
  have hupper := le_of_test_integrals hs hf hg (fun b hb hc hbs hpos =>
    (le_abs_self _).trans (htest b hb hc hbs hpos))
  have hlower := le_of_test_integrals hs hf.neg hg (f := fun t => -f t) (by
    intro b hb hc hbs hpos
    have h := htest b hb hc hbs hpos
    simp only [mul_neg, integral_neg]
    exact (neg_le_abs _).trans h)
  intro t ht
  exact abs_le.mpr ⟨by linarith [hlower t ht], hupper t ht⟩

/-- Squares of smooth compact tests already suffice. This form allows the
same time cutoff to localize both the equation and its vector test. -/
theorem le_of_square_test_integrals {s : Set ℝ} (hs : IsOpen s) {f g : ℝ → ℝ}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (htest : ∀ b : ℝ → ℝ, ContDiff ℝ ∞ b → HasCompactSupport b → tsupport b ⊆ s →
      (∫ t : ℝ, b t ^ 2 * f t) ≤ ∫ t : ℝ, b t ^ 2 * g t) :
    ∀ t ∈ s, f t ≤ g t := by
  intro t ht
  by_contra hn
  have hpos : 0 < f t - g t := sub_pos.mpr (lt_of_not_ge hn)
  have hnh : s ∩ {r | 0 < f r - g r} ∈ 𝓝 t :=
    inter_mem (hs.mem_nhds ht) (((hf.sub hg).continuousAt (hs.mem_nhds ht)) (Ioi_mem_nhds hpos))
  obtain ⟨b, hbs, hbc, hbd, _, hbt⟩ := exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) hnh
  have hbs' : tsupport b ⊆ s := hbs.trans inter_subset_left
  let c : ℝ → ℝ := fun r => b r ^ 2
  have hsq : HasCompactSupport c := hbc.comp_left (g := fun x : ℝ => x ^ 2) (by norm_num)
  have hsqS : tsupport c ⊆ s :=
    (tsupport_comp_subset (g := fun x : ℝ => x ^ 2) (by norm_num) b).trans hbs'
  have hcc : Continuous c := hbd.continuous.pow 2
  have hcont : Continuous (fun r => c r * (f r - g r)) :=
    continuous_test_product hs hcc (hf.sub hg) hsqS
  have hcprod : HasCompactSupport (fun r => c r * (f r - g r)) := hsq.mul_right
  have hnonneg (r : ℝ) : 0 ≤ c r * (f r - g r) := by
    by_cases hr : b r = 0
    · simp [c, hr]
    · exact mul_nonneg (sq_nonneg _) (hbs (subset_tsupport _ hr)).2.le
  have hint : 0 < ∫ r : ℝ, c r * (f r - g r) :=
    hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := t) hcprod hnonneg
      (by simpa only [c, hbt, one_pow, one_mul] using hpos.ne')
  have hiF : Integrable (fun r => c r * f r) :=
    (continuous_test_product hs hcc hf hsqS).integrable_of_hasCompactSupport hsq.mul_right
  have hiG : Integrable (fun r => c r * g r) :=
    (continuous_test_product hs hcc hg hsqS).integrable_of_hasCompactSupport hsq.mul_right
  simp_rw [mul_sub] at hint
  rw [integral_sub hiF hiG] at hint
  have hh : (∫ r : ℝ, c r * f r) ≤ ∫ r : ℝ, c r * g r := htest b hbd hbc hbs'
  linarith

theorem abs_le_of_square_test_integrals {s : Set ℝ} (hs : IsOpen s) {f g : ℝ → ℝ}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (htest : ∀ b : ℝ → ℝ, ContDiff ℝ ∞ b → HasCompactSupport b → tsupport b ⊆ s →
      |∫ t : ℝ, b t ^ 2 * f t| ≤ ∫ t : ℝ, b t ^ 2 * g t) :
    ∀ t ∈ s, |f t| ≤ g t := by
  have hupper := le_of_square_test_integrals hs hf hg (fun b hb hc hbs =>
    (le_abs_self _).trans (htest b hb hc hbs))
  have hlower := le_of_square_test_integrals hs hf.neg hg (f := fun t => -f t) (by
    intro b hb hc hbs
    simp only [mul_neg, integral_neg]
    exact (neg_le_abs _).trans (htest b hb hc hbs))
  intro t ht
  exact abs_le.mpr ⟨by linarith [hlower t ht], hupper t ht⟩

end NavierStokes.R3PositiveTests
