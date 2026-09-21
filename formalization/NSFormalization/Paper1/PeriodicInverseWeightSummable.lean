import NSFormalization.Paper1.PeriodicSobolevHilbert
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! Inverse Bessel weight summability on the actual integer lattice.
No summability or cutoff-dependent constant is assumed. -/
noncomputable section
namespace NSFormalization.Paper1.PeriodicInverseWeightSummable
open scoped BigOperators

private theorem coordinate_summable :
    Summable (fun n : ℤ => 1 / (1 + (n : ℝ)^2)) := by
  have hp : Summable (fun n : ℤ => 1 / (n : ℝ)^2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  have hz : Summable (fun n : ℤ => if n = 0 then (1 : ℝ) else 0) :=
    (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable
  apply (hz.add hp).of_nonneg_of_le
  · intro n; positivity
  · intro n
    by_cases hn : n = 0
    · subst n; norm_num
    · simp only [ite_eq_right (by exact hn), zero_add]
      apply one_div_le_one_div_of_le
      · exact sq_pos_of_ne_zero (by exact_mod_cast hn)
      · linarith [sq_nonneg (n : ℝ)]

private theorem coordinate_weight_le (k : PeriodicFrequency) (i : Fin 3) :
    1 + (k i : ℝ)^2 ≤ periodicFrequencyWeight k := by
  rw [periodicFrequencyWeight_eq]
  have hsum : (k i : ℝ)^2 ≤ ∑ j : Fin 3, (k j : ℝ)^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (k j : ℝ)) (Finset.mem_univ i)
  have hpi : 1 ≤ (2 * Real.pi)^2 := by nlinarith [Real.two_le_pi]
  have hnonneg : 0 ≤ ∑ j : Fin 3, (k j : ℝ)^2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  nlinarith

private theorem coordinate_product_summable :
    Summable (fun k : PeriodicFrequency =>
      (1 / (1 + (k 0 : ℝ)^2)) * (1 / (1 + (k 1 : ℝ)^2)) *
        (1 / (1 + (k 2 : ℝ)^2))) := by
  have ha := coordinate_summable
  have hn : (0 : ℤ → ℝ) ≤ (fun n : ℤ => 1 / (1 + (n : ℝ)^2)) := by
    intro n; positivity
  have hab := ha.mul_of_nonneg ha hn hn
  have habc := hab.mul_of_nonneg ha (fun n => mul_nonneg (hn n.1) (hn n.2)) hn
  apply habc.comp_injective (i := fun k : PeriodicFrequency => ((k 0, k 1), k 2))
  intro k l h
  have h0 : k 0 = l 0 := congrArg (fun p : (ℤ × ℤ) × ℤ => p.1.1) h
  have h1 : k 1 = l 1 := congrArg (fun p : (ℤ × ℤ) × ℤ => p.1.2) h
  have h2 : k 2 = l 2 := congrArg (fun p : (ℤ × ℤ) × ℤ => p.2) h
  funext i
  fin_cases i <;> assumption

/-- Inverse cubes of the native Bessel weight are summable over all of Z³. -/
theorem summable_inverse_weight_cube :
    Summable (fun k : PeriodicFrequency => (periodicFrequencyWeight k ^ (3 : ℕ))⁻¹) := by
  apply coordinate_product_summable.of_nonneg_of_le
  · intro k
    exact inv_nonneg.mpr (pow_nonneg ((one_le_periodicFrequencyWeight k).trans' zero_le_one) _)
  · intro k
    have hw : 0 < periodicFrequencyWeight k := lt_of_lt_of_le zero_lt_one (one_le_periodicFrequencyWeight k)
    have hprod :
        (1 + (k 0 : ℝ)^2) * (1 + (k 1 : ℝ)^2) * (1 + (k 2 : ℝ)^2) ≤
          periodicFrequencyWeight k ^ (3 : ℕ) := by
      calc
        _ ≤ (periodicFrequencyWeight k * periodicFrequencyWeight k) * periodicFrequencyWeight k :=
          mul_le_mul (mul_le_mul (coordinate_weight_le k 0) (coordinate_weight_le k 1)
            (by positivity) hw.le) (coordinate_weight_le k 2) (by positivity) (by positivity)
        _ = _ := by ring
    simpa only [one_div, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using
      one_div_le_one_div_of_le (by positivity : 0 <
        (1 + (k 0 : ℝ)^2) * (1 + (k 1 : ℝ)^2) * (1 + (k 2 : ℝ)^2)) hprod

/-- Real-power form used by the project's Fourier Sobolev norm. -/
theorem summable_weight_rpow_neg_three :
    Summable (fun k : PeriodicFrequency => periodicFrequencyWeight k ^ (-3 : ℝ)) := by
  convert summable_inverse_weight_cube using 1
  ext k
  rw [Real.rpow_neg (le_trans zero_le_one (one_le_periodicFrequencyWeight k))]
  norm_num

end NSFormalization.Paper1.PeriodicInverseWeightSummable
