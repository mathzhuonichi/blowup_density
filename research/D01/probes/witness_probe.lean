import NSFormalization.Paper3.SobolevHilbertModel
import NSFormalization.Source.RealSobolev

open MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source.RealSobolev (FourierData)

namespace Probe
noncomputable section

-- reuse verified pieces (copied)
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
  apply Real.sqrt_le_sqrt; rw [hQ]; nlinarith [hSQ, hS]

theorem continuous_sobolevBesselWeight_one : Continuous (sobolevBesselWeight 1) := by
  unfold sobolevBesselWeight
  refine Complex.continuous_ofReal.comp (Continuous.rpow_const ?_ ?_)
  · fun_prop
  · intro ξ; exact Or.inl (by positivity : (0:ℝ) < 1 + ‖ξ‖ ^ 2).ne'

-- THE BRIDGE
theorem raisableWitness_of_memLp_smul (h : FourierData)
    (hcoord : ∀ j : Fin 3, MemLp (fun ξ => (ξ j : ℂ) • (h : Space → ℂ) ξ) 2 volume) :
    MemLp (fun ξ => sobolevBesselWeight 1 ξ • (h : Space → ℂ) ξ) 2 volume := by
  have hhL2 : MemLp (fun ξ => (h : Space → ℂ) ξ) 2 volume := Lp.memLp h
  -- dominating real function
  set F : Space → ℝ := fun ξ => ‖(h : Space → ℂ) ξ‖ + ∑ j : Fin 3, ‖(ξ j : ℂ) • (h : Space → ℂ) ξ‖ with hF
  have hsum : MemLp (fun ξ => ∑ j : Fin 3, ‖(ξ j : ℂ) • (h : Space → ℂ) ξ‖) 2 volume := by
    simp only [Fin.sum_univ_three]
    exact ((hcoord 0).norm.add (hcoord 1).norm).add (hcoord 2).norm
  have hFmem : MemLp F 2 volume := hhL2.norm.add hsum
  have haesm : AEStronglyMeasurable (fun ξ => sobolevBesselWeight 1 ξ • (h : Space → ℂ) ξ) volume :=
    (continuous_sobolevBesselWeight_one.aestronglyMeasurable).smul (Lp.aestronglyMeasurable h)
  refine MemLp.mono' hFmem haesm ?_
  filter_upwards with ξ
  rw [norm_smul, norm_sobolevBesselWeight_one, hF]
  have hbound : Real.sqrt (1 + ‖ξ‖ ^ 2) * ‖(h:Space→ℂ) ξ‖
      ≤ ‖(h:Space→ℂ) ξ‖ + ∑ j : Fin 3, |ξ j| * ‖(h:Space→ℂ) ξ‖ := by
    rw [← Finset.sum_mul]
    have h1 := mul_le_mul_of_nonneg_right (sqrt_one_add_normSq_le ξ) (norm_nonneg ((h:Space→ℂ) ξ))
    rwa [add_mul, one_mul] at h1
  refine hbound.trans (le_of_eq ?_)
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]

end
end Probe
