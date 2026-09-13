import NSFormalization.Paper1.PeriodicPicardDifferenceBound
import NSFormalization.Paper1.PeriodicHeatMultiplier

noncomputable section
namespace NSFormalization.Paper1.PeriodicPicardDifferenceHeatBound

open NSFormalization.Paper1.PeriodicHeatMultiplier
open NSFormalization.Paper1.PeriodicPicardDifferenceBound
open NSFormalization.Paper1.PeriodicPicardBilinear

abbrev FiniteFourier := PeriodicPicardBilinear.FiniteFourier

/-! Heat-weighted coefficient bound. This is still a finite-frequency estimate;
no time integration or contraction assertion is made. -/
theorem norm_heat_mul_quad_difference_le
    {ν s : ℝ} (hν : 0 ≤ ν) (hs : 0 ≤ s)
    (u v : FiniteFourier) (n : PeriodicFrequency) :
    ‖(heatSymbol ν s n : ℂ) *
        (convolutionCoeff u u n - convolutionCoeff v v n)‖ ≤
      (∑ k ∈ (u - v).support.filter (fun k => u (n - k) ≠ 0),
        ‖(u - v) k‖ * ‖u (n - k)‖) +
      (∑ k ∈ v.support.filter (fun k => (u - v) (n - k) ≠ 0),
        ‖v k‖ * ‖(u - v) (n - k)‖) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (heatSymbol_nonneg _ _ _)]
  exact le_trans (mul_le_mul_of_nonneg_left (norm_convolutionCoeff_quad_difference_le u v n)
      (heatSymbol_nonneg ν s n)) (mul_le_of_le_one_left (add_nonneg
    (Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    (heatSymbol_le_one hν hs n))

end NSFormalization.Paper1.PeriodicPicardDifferenceHeatBound
