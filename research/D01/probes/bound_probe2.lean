import NSFormalization.Paper3.SobolevHilbertModel
import NSFormalization.Source.RealSobolev

open MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source.RealSobolev (FourierData)

namespace Probe
noncomputable section

theorem norm_sobolevBesselWeight_one (ξ : Space) :
    ‖sobolevBesselWeight 1 ξ‖ = Real.sqrt (1 + ‖ξ‖ ^ 2) := by
  rw [sobolevBesselWeight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), Real.sqrt_eq_rpow]

theorem sqrt_one_add_normSq_le (ξ : Space) :
    Real.sqrt (1 + ‖ξ‖ ^ 2) ≤ 1 + ∑ j : Fin 3, |ξ j| := by
  have hQ : ‖ξ‖ ^ 2 = ∑ j : Fin 3, (ξ j) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    congr 1; funext j; rw [Real.norm_eq_abs, sq_abs]
  have hSQ : ∑ j : Fin 3, (ξ j) ^ 2 ≤ (∑ j : Fin 3, |ξ j|) ^ 2 := by
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    nlinarith [mul_nonneg (abs_nonneg (ξ 0)) (abs_nonneg (ξ 1)),
      mul_nonneg (abs_nonneg (ξ 0)) (abs_nonneg (ξ 2)),
      mul_nonneg (abs_nonneg (ξ 1)) (abs_nonneg (ξ 2)),
      sq_abs (ξ 0), sq_abs (ξ 1), sq_abs (ξ 2)]
  have hS : 0 ≤ ∑ j : Fin 3, |ξ j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  rw [show (1 : ℝ) + ∑ j : Fin 3, |ξ j| = Real.sqrt ((1 + ∑ j : Fin 3, |ξ j|) ^ 2) from
    (Real.sqrt_sq (by linarith)).symm]
  apply Real.sqrt_le_sqrt
  rw [hQ]; nlinarith [hSQ, hS]

theorem norm_raiseIntegrand_le (h : FourierData) (ξ : Space) :
    ‖sobolevBesselWeight 1 ξ • (h : Space → ℂ) ξ‖
      ≤ ‖(h : Space → ℂ) ξ‖ + ∑ j : Fin 3, |ξ j| * ‖(h : Space → ℂ) ξ‖ := by
  rw [norm_smul, norm_sobolevBesselWeight_one, ← Finset.sum_mul]
  have h1 := mul_le_mul_of_nonneg_right (sqrt_one_add_normSq_le ξ) (norm_nonneg ((h : Space → ℂ) ξ))
  rwa [add_mul, one_mul] at h1

end
end Probe
