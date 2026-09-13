import NSFormalization.Source.RieszFourierScale
import NSFormalization.Source.RieszSchwartzPairing

noncomputable section
namespace NSFormalization.Source.RieszFourierProfilePower
open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Source.RieszFourierScale
open NSFormalization.Source.RieszGaussianMixture

def constant (a : ℝ) : ℝ :=
  Real.pi ^ (3 / 2 - a) * Real.Gamma (a / 2) / Real.Gamma ((3-a)/2)

theorem integral_fourierProfile_power {a : ℝ} (ha : 0 < a) {ξ : Space} (hξ : ξ ≠ 0) :
    (∫ t : ℝ in Ioi 0, fourierProfile a ξ t) = constant a * ‖ξ‖ ^ (-a) := by
  rw [integral_fourierProfile ha hξ]
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hp : (Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (a / 2) = Real.pi ^ a * ‖ξ‖ ^ a := by
    rw [Real.mul_rpow (sq_nonneg _) (sq_nonneg _)]
    simp only [← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le, ← Real.rpow_mul hn.le]
    congr 1 <;> congr 1 <;> ring
  rw [hp, Real.rpow_neg hn.le]
  unfold constant
  rw [Real.rpow_sub Real.pi_pos]
  ring

theorem fourierProfile_nonneg {a t : ℝ} (ha3 : a < 3) (ht : 0 < t) (ξ : Space) :
    0 ≤ fourierProfile a ξ t := by
  unfold fourierProfile scaleWeight
  have hG := Real.Gamma_pos_of_pos (show 0 < (3-a)/2 by linarith)
  positivity

end NSFormalization.Source.RieszFourierProfilePower
