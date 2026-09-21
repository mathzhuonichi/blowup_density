import NavierStokes.R3.WholeSpaceUniqueness

/-! The only extra boundary term for a bounded, noncompact reference velocity. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff BigOperators InnerProductSpace
namespace NSFormalization.Source.BoundedReferenceFlux
open NavierStokesR3 NavierStokesR3.ProblemStatement NavierStokesR3.Comparison
  NavierStokesR3.LocalizedFluxEstimates

theorem transport_flux_bound {φ : Space → ℝ} {u v : VelocityField} {t : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ)
    (hu : Continuous (fun x => u (t, x))) (hv : Continuous (fun x => v (t, x)))
    (hw2 : MemLp (fun x => (u - v) (t, x)) 2 volume)
    (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    {L U : ℝ} (hL0 : 0 ≤ L) (hL : ∀ x, ‖fderiv ℝ φ x‖ ≤ L)
    (hU0 : 0 ≤ U) (hU : ∀ x, ‖u (t, x)‖ ≤ U) :
    |∫ x, ‖(u - v) (t, x)‖ ^ 2 * fderiv ℝ (fun y => φ y ^ 8) x (v (t, x))| ≤
      (8 * L) * comparisonLpNorm 2 (fun x => (u - v) (t, x)) ^ (3 / 2 : ℝ) *
        cutoffL6 φ (u - v) t ^ (3 / 2 : ℝ) +
      (8 * L * U) * comparisonLpNorm 2 (fun x => (u - v) (t, x)) ^ 2 := by
  have hw : Continuous (fun x => (u - v) (t, x)) := hu.sub hv
  have hweighted := WeightedSobolev.memLp_cutoff_pow_smul hφ.continuous hs hw
    (by norm_num : (4 : ℕ) ≠ 0) 6
  obtain ⟨hT, hTb⟩ := WeightedInterpolation.cutoff_transport_bound
    hφ.continuous.aestronglyMeasurable hφ0 hw2 hweighted
  have hsquare : Integrable (fun x => ‖(u-v) (t,x)‖^2) :=
    (memLp_two_iff_integrable_sq_norm hw2.aestronglyMeasurable).mp hw2
  have hmajor := (hT.const_mul (8 * L)).add (hsquare.const_mul (8 * L * U))
  have hdU (x : Space) : ‖fderiv ℝ (fun y => φ y ^ 8) x (u (t,x))‖ ≤ 8 * L * U := by
    have hpow : φ x ^ 6 ≤ 1 := pow_le_one₀ (hφ0 x) (hφ1 x)
    calc
      _ ≤ (8 * L) * φ x ^ 6 * ‖u (t,x)‖ :=
        norm_fderiv_cutoff_eight_apply_le (hφ.differentiable (by simp) x)
          (hφ0 x) (hφ1 x) hL0 (hL x) _
      _ ≤ (8 * L) * 1 * U := mul_le_mul
        (mul_le_mul_of_nonneg_left hpow (by positivity)) (hU x)
        (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hsplit (x : Space) : fderiv ℝ (fun y => φ y ^ 8) x (v (t,x)) =
      fderiv ℝ (fun y => φ y ^ 8) x (u (t,x)) -
      fderiv ℝ (fun y => φ y ^ 8) x ((u-v) (t,x)) := by
    simp only [Pi.sub_apply, map_sub]
    abel
  have hbound (x : Space) :
      ‖‖(u-v) (t,x)‖^2 * fderiv ℝ (fun y => φ y^8) x (v (t,x))‖ ≤
        (8*L) * (φ x^6 * ‖(u-v) (t,x)‖^3) + (8*L*U) * ‖(u-v) (t,x)‖^2 := by
    rw [norm_mul, norm_pow, norm_norm, hsplit]
    have hd := norm_fderiv_cutoff_eight_apply_le (hφ.differentiable (by simp) x)
      (hφ0 x) (hφ1 x) hL0 (hL x) ((u-v) (t,x))
    calc
      _ ≤ ‖(u-v) (t,x)‖^2 * (‖fderiv ℝ (fun y => φ y^8) x (u (t,x))‖ +
          ‖fderiv ℝ (fun y => φ y^8) x ((u-v) (t,x))‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (sq_nonneg _)
      _ ≤ ‖(u-v) (t,x)‖^2 * ((8*L*U) + (8*L)*φ x^6*‖(u-v) (t,x)‖) :=
        mul_le_mul_of_nonneg_left (add_le_add (hdU x) hd) (sq_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ ∫ x, (8*L) * (φ x^6 * ‖(u-v) (t,x)‖^3) + (8*L*U) * ‖(u-v) (t,x)‖^2 :=
      norm_integral_le_of_norm_le hmajor (Eventually.of_forall hbound)
    _ = (8*L) * (∫ x, φ x^6 * ‖(u-v) (t,x)‖^3) +
        (8*L*U) * comparisonLpNorm 2 (fun x => (u-v) (t,x))^2 := by
      rw [integral_add (hT.const_mul _) (hsquare.const_mul _), integral_const_mul,
        integral_const_mul]
      have he := LpNormTools.lpNorm_two_sq_eq_l2Sq hw2
      change comparisonLpNorm 2 (fun x => (u-v) (t,x)) ^ 2 =
        (∫ x, ‖(u-v) (t,x)‖ ^ 2) at he
      rw [he]
    _ ≤ _ := by
      apply add_le_add
      · simpa only [mul_assoc, cutoffL6] using
          mul_le_mul_of_nonneg_left hTb (by positivity : 0 ≤ 8*L)
      · exact le_rfl
end NSFormalization.Source.BoundedReferenceFlux
