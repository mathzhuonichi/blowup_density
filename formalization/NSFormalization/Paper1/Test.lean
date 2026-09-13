import NSFormalization.Paper1.PeriodicH2Embedding
import Mathlib.Algebra.Order.Chebyshev
open MeasureTheory
open scoped BigOperators
namespace NSFormalization.Paper1
open NavierStokes.ProblemStatement
example (k : PeriodicFrequency) :
    ‖(fun i => (k i : ℝ))‖ ^ 2 ≤ 3 * ∑ i : Fin 3, (k i : ℝ)^2 := by
  have hsum : ‖(fun i => (k i : ℝ))‖ ≤ ∑ i : Fin 3, |(k i : ℝ)| := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    simpa only [Real.norm_eq_abs, Finset.sum_filter, Finset.filter_true_of_mem] using
      (Finset.single_le_sum (s := (Finset.univ : Finset (Fin 3)))
        (f := fun j : Fin 3 => |(k j : ℝ)|)
        (fun j _ => abs_nonneg _) (Finset.mem_univ i))
  have hsq := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 3)))
      (f := fun i : Fin 3 => |(k i : ℝ)|)
  have hcard : (Finset.univ : Finset (Fin 3)).card = 3 := by simp
  rw [hcard] at hsq
  have hsq' := hsq
  norm_num [hcard, sq_abs] at hsq'
  have hnon : 0 ≤ ‖(fun i => (k i : ℝ))‖ := norm_nonneg _
  have hsum0 : 0 ≤ ∑ i : Fin 3, |(k i : ℝ)| := by positivity
  nlinarith [sq_nonneg (∑ i : Fin 3, |(k i : ℝ)| - ‖(fun i => (k i : ℝ))‖)]
end NSFormalization.Paper1
namespace NSFormalization.Paper1
open NavierStokes.ProblemStatement
example (k : PeriodicFrequency) :
    ‖(fun i => (k i : ℝ))‖ ^ 2 ≤ periodicFrequencyWeight k := by
  rw [periodicFrequencyWeight_eq]
  have hsum : 0 ≤ ∑ i : Fin 3, (k i : ℝ)^2 := by positivity
  have hnormsq : ‖(fun i => (k i : ℝ))‖ ^ 2 ≤ 3 * ∑ i : Fin 3, (k i : ℝ)^2 := by
    have hsumabs : ‖(fun i => (k i : ℝ))‖ ≤ ∑ i : Fin 3, |(k i : ℝ)| := by
      rw [pi_norm_le_iff_of_nonneg (by positivity)]
      intro i
      simpa only [Real.norm_eq_abs, Finset.sum_filter, Finset.filter_true_of_mem] using
        (Finset.single_le_sum (s := (Finset.univ : Finset (Fin 3)))
          (f := fun j : Fin 3 => |(k j : ℝ)|)
          (fun j _ => abs_nonneg _) (Finset.mem_univ i))
    have hsq := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 3)))
      (f := fun i : Fin 3 => |(k i : ℝ)|)
    have hcard : (Finset.univ : Finset (Fin 3)).card = 3 := by simp
    norm_num [hcard, sq_abs] at hsq
    have hsumabs0 : 0 ≤ ∑ i : Fin 3, |(k i : ℝ)| := by positivity
    nlinarith
  have hpi : 3 ≤ (2 * Real.pi) ^ 2 := by
    have hp : (3 : ℝ) < Real.pi := Real.pi_gt_three
    nlinarith [sq_nonneg (Real.pi - 3)]
  nlinarith
end NSFormalization.Paper1
